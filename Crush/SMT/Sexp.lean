import Lean

/-!
# S-expression parser for SMT-LIB solver output

Solver responses (`get-unsat-core`, `get-model`, `get-proof`) come back as
S-expressions. We parse them into a small `Sexp` tree so downstream code can walk
them structurally instead of slicing the output with string operations.

The parser is deliberately permissive: it recognizes atoms, string literals (with
SMT-LIB `""` escaping), and parenthesized lists, and skips `;` line comments and
whitespace. It does not interpret the atoms — that is the caller's job.
-/

namespace Crush.SMT

/-- A parsed S-expression: an atom (symbol/number/keyword) or a list. String
literals are kept as atoms with their surrounding quotes stripped and marked. -/
inductive Sexp where
  | atom : String → Sexp
  | str  : String → Sexp
  | list : Array Sexp → Sexp
  deriving Inhabited, Repr, BEq

namespace Sexp

-- Nested inductive over `Array`, so the recursion goes through a list helper to
-- make the descent structural (see the note in `SMT/Print.lean`).
mutual
  /-- Render back to text (round-trips structurally, not byte-for-byte). -/
  def toString : Sexp → String
    | .atom s => s
    | .str s  => "\"" ++ s.replace "\"" "\"\"" ++ "\""
    | .list xs => "(" ++ String.intercalate " " (toStringList xs.toList) ++ ")"
  termination_by x => sizeOf x
  decreasing_by obtain ⟨l⟩ := xs; simp [Array.mk.sizeOf_spec]; omega

  def toStringList : List Sexp → List String
    | [] => []
    | x :: xs => toString x :: toStringList xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals (simp_wf; omega)
end

instance : ToString Sexp := ⟨toString⟩

/-- The atom string, if this is an atom (not a list or string literal). -/
def atom? : Sexp → Option String
  | .atom s => some s
  | _ => none

/-- The elements, if this is a list. -/
def list? : Sexp → Option (Array Sexp)
  | .list xs => some xs
  | _ => none

end Sexp

namespace SexpParser

/-- Parser state: the input and a cursor position (byte index into `s.toList`).
We work over `List Char` for simple, total, structurally-recursive parsing. -/
structure St where
  chars : List Char
  deriving Inhabited

private def isDelim (c : Char) : Bool :=
  c == '(' || c == ')' || c.isWhitespace || c == ';' || c == '"'

/-- `dropWhile` never lengthens a list. Needed for `skipTrivia`'s termination and not
present in core, so proved here. -/
private theorem length_dropWhile_le (p : Char → Bool) (l : List Char) :
    (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons c cs ih => simp only [List.dropWhile]; split <;> simp_all <;> omega

/-- Drop leading whitespace and `;`-to-EOL comments. -/
def skipTrivia : List Char → List Char
  | [] => []
  | c :: rest =>
    if c.isWhitespace then skipTrivia rest
    else if c == ';' then skipTrivia (rest.dropWhile (· != '\n'))
    else c :: rest
termination_by cs => cs.length
decreasing_by
  -- The whitespace branch drops one character; the comment branch drops one and
  -- then a prefix, and `dropWhile` never lengthens a list.
  · simp_wf
  · simp_wf; exact Nat.lt_succ_of_le (length_dropWhile_le _ _)

/-- Parse a `"..."` string literal body (cursor is just past the opening quote).
Handles the SMT-LIB `""` escape for a literal double-quote. -/
def parseString (acc : String) : List Char → Option (String × List Char)
  | [] => none
  | '"' :: '"' :: rest => parseString (acc.push '"') rest
  | '"' :: rest => some (acc, rest)
  | c :: rest => parseString (acc.push c) rest
termination_by cs => cs.length

/-- Parse a bare atom up to the next delimiter. -/
def parseAtom (acc : String) : List Char → String × List Char
  | [] => (acc, [])
  | c :: rest =>
    if isDelim c then (acc, c :: rest)
    else parseAtom (acc.push c) rest
termination_by cs => cs.length

/-! Termination of the parser proper.

`parseList` recurses on whatever `parseOne` *returned*, so a direct measure on the
input would need a theorem saying "`parseOne` consumes at least one character" —
which is a statement about `parseOne` that `parseOne`'s own definition would then
depend on. Rather than tie the definition to its own correctness proof, both
functions take an explicit `fuel` bound: each recursive call decreases it, so
termination is immediate and structural.

Fuel is not a fudge here. `parseSexps` supplies `cs.length`, and each nested
S-expression consumes at least the character that opened it, so the budget cannot be
exhausted on well-formed input — running out is reported as a parse failure
(`none`), which is exactly how malformed input is already handled. The alternative
(proving the consumption lemma and using it in a well-founded measure) buys nothing
here, since the parser's result is checked by the caller either way. -/
mutual
  /-- Parse one S-expression. Returns the parsed value and the remaining input. -/
  def parseOne (fuel : Nat) (cs : List Char) : Option (Sexp × List Char) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match skipTrivia cs with
      | [] => none
      | '(' :: rest => do
        let (elems, rest') ← parseList fuel #[] rest
        return (.list elems, rest')
      | ')' :: _ => none
      | '"' :: rest => do
        let (s, rest') ← parseString "" rest
        return (.str s, rest')
      | cs' =>
        let (a, rest') := parseAtom "" cs'
        if a.isEmpty then none else some (.atom a, rest')

  /-- Parse list elements until the matching `)`. -/
  def parseList (fuel : Nat) (acc : Array Sexp) (cs : List Char) :
      Option (Array Sexp × List Char) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match skipTrivia cs with
      | [] => none
      | ')' :: rest => some (acc, rest)
      | cs' => do
        let (e, rest) ← parseOne fuel cs'
        parseList fuel (acc.push e) rest
end

end SexpParser

/-- Parse a single S-expression from the front of `s`, returning it and the
unconsumed remainder. `none` on malformed/empty input. -/
def parseSexp (s : String) : Option (Sexp × String) := do
  -- One unit of fuel per input character: more than enough, since every nested
  -- S-expression consumes at least its opening paren.
  let cs := s.toList
  let (e, rest) ← SexpParser.parseOne (cs.length + 1) cs
  return (e, String.ofList rest)

/-- Parse every S-expression in `s` (e.g. a solver dumps several in a row).

The `rounds` bound makes this total. It also guards against a subtle hazard the
previous `repeat` loop had: if `parseOne` ever returned without consuming input, the
loop would spin forever. Here it simply stops. One round per character is ample,
since each successful parse consumes at least one. -/
def parseSexpsAux (rounds : Nat) (acc : Array Sexp) (cs : List Char) : Array Sexp :=
  match rounds with
  | 0 => acc
  | rounds + 1 =>
    match SexpParser.parseOne (cs.length + 1) cs with
    | none => acc
    | some (e, rest) => parseSexpsAux rounds (acc.push e) rest

def parseSexps (s : String) : Array Sexp :=
  let cs := s.toList
  parseSexpsAux (cs.length + 1) #[] cs

end Crush.SMT
