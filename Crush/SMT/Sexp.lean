import Lean

/-!
# S-expression parser for SMT-LIB solver output

Solver responses (`get-unsat-core`, `get-model`, `get-proof`) come back as
S-expressions. We parse them into a small `Sexp` tree so downstream code can walk
them structurally instead of doing string surgery — the fragile approach in
lean-auto's `Solver/SMT.lean`, which sliced output by hand.

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

/-- Render back to text (round-trips structurally, not byte-for-byte). -/
partial def toString : Sexp → String
  | .atom s => s
  | .str s  => "\"" ++ s.replace "\"" "\"\"" ++ "\""
  | .list xs => "(" ++ String.intercalate " " (xs.toList.map toString) ++ ")"

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

/-- Drop leading whitespace and `;`-to-EOL comments. -/
partial def skipTrivia : List Char → List Char
  | [] => []
  | c :: rest =>
    if c.isWhitespace then skipTrivia rest
    else if c == ';' then skipTrivia (rest.dropWhile (· != '\n'))
    else c :: rest

/-- Parse a `"..."` string literal body (cursor is just past the opening quote).
Handles the SMT-LIB `""` escape for a literal double-quote. -/
partial def parseString (acc : String) : List Char → Option (String × List Char)
  | [] => none
  | '"' :: '"' :: rest => parseString (acc.push '"') rest
  | '"' :: rest => some (acc, rest)
  | c :: rest => parseString (acc.push c) rest

/-- Parse a bare atom up to the next delimiter. -/
partial def parseAtom (acc : String) : List Char → String × List Char
  | [] => (acc, [])
  | c :: rest =>
    if isDelim c then (acc, c :: rest)
    else parseAtom (acc.push c) rest

mutual
  /-- Parse one S-expression. Returns the parsed value and the remaining input. -/
  partial def parseOne (cs : List Char) : Option (Sexp × List Char) :=
    match skipTrivia cs with
    | [] => none
    | '(' :: rest => do
      let (elems, rest') ← parseList #[] rest
      return (.list elems, rest')
    | ')' :: _ => none
    | '"' :: rest => do
      let (s, rest') ← parseString "" rest
      return (.str s, rest')
    | cs' =>
      let (a, rest') := parseAtom "" cs'
      if a.isEmpty then none else some (.atom a, rest')

  /-- Parse list elements until the matching `)`. -/
  partial def parseList (acc : Array Sexp) (cs : List Char) : Option (Array Sexp × List Char) :=
    match skipTrivia cs with
    | [] => none
    | ')' :: rest => some (acc, rest)
    | cs' => do
      let (e, rest) ← parseOne cs'
      parseList (acc.push e) rest
end

end SexpParser

/-- Parse a single S-expression from the front of `s`, returning it and the
unconsumed remainder. `none` on malformed/empty input. -/
def parseSexp (s : String) : Option (Sexp × String) := do
  let (e, rest) ← SexpParser.parseOne s.toList
  return (e, String.ofList rest)

/-- Parse every S-expression in `s` (e.g. a solver dumps several in a row). -/
partial def parseSexps (s : String) : Array Sexp := Id.run do
  let mut out := #[]
  let mut cs := s.toList
  repeat
    match SexpParser.parseOne cs with
    | none => break
    | some (e, rest) =>
      out := out.push e
      cs := rest
  return out

end Crush.SMT
