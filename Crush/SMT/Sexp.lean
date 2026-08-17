import Lean

/-!
# S-expression parser for SMT-LIB solver output

Solver responses (`get-unsat-core`, `get-model`, `get-proof`) come back as
S-expressions. We parse them into a small `Sexp` tree so downstream code can walk
them structurally instead of slicing the output with string operations.

The parser recognizes bare and `|…|`-quoted symbols, string literals (with SMT-LIB
`""` escaping), and parenthesized lists, and skips `;` line comments and whitespace.
Malformed or truncated trailing input rejects the complete parse rather than
returning a misleading prefix. It does not interpret atoms — that is the caller's
job.

The scanner reads UTF-8 bytes directly and produces atoms and quoted symbols with a
single `String.extract` over the matched span. SMT-LIB's structural characters and
whitespace are ASCII, so scanning bytes avoids decoding every non-structural character.
Recursion is bounded by an explicit fuel argument — one unit per remaining byte, and
every step consumes at least one — so these are total definitions rather than `partial`
ones.
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

/-- Whether this is a list S-expression. -/
def isList : Sexp → Bool
  | .list _ => true
  | _ => false

end Sexp

namespace SexpParser

/-- An untyped byte offset into the input, since `String.Pos` is indexed by its
string. -/
abbrev Pos := String.Pos.Raw

@[inline] private def after (i : Pos) : Pos := ⟨i.byteIdx + 1⟩
@[inline] private def byteAt (s : String) (i : Pos) (h : i < s.rawEndPos) : UInt8 :=
  s.getUTF8Byte i h
@[inline] private def span (s : String) (b e : Pos) : String := String.Pos.Raw.extract s b e

@[inline] private def isWhitespace (c : UInt8) : Bool :=
  c == '\t'.toUInt8 || c == '\n'.toUInt8 || c == '\r'.toUInt8 || c == ' '.toUInt8

@[inline] private def isDelim (c : UInt8) : Bool :=
  c == '('.toUInt8 || c == ')'.toUInt8 || isWhitespace c || c == ';'.toUInt8 ||
    c == '"'.toUInt8 || c == '|'.toUInt8

/-- Position of the next newline at or after `i` (or end of input). -/
def lineEnd (s : String) : Pos → Nat → Pos
  | i, 0 => i
  | i, fuel + 1 =>
    if h : i < s.rawEndPos then
      if byteAt s i h == '\n'.toUInt8 then i else lineEnd s (after i) fuel
    else i

/-- Position after leading whitespace and `;`-to-end-of-line comments. -/
def skipTrivia (s : String) : Pos → Nat → Pos
  | i, 0 => i
  | i, fuel + 1 =>
    if h : i < s.rawEndPos then
      let c := byteAt s i h
      if isWhitespace c then skipTrivia s (after i) fuel
      else if c == ';'.toUInt8 then skipTrivia s (lineEnd s (after i) fuel) fuel
      else i
    else i

/-- End of the bare atom starting at `i`, i.e. the next delimiter or end of input. -/
def atomEnd (s : String) : Pos → Nat → Pos
  | i, 0 => i
  | i, fuel + 1 =>
    if h : i < s.rawEndPos then
      if isDelim (byteAt s i h) then i else atomEnd s (after i) fuel
    else i

/-- Parse a `"..."` string literal body (cursor is just past the opening quote).
Handles the SMT-LIB `""` escape for a literal double-quote, which is why this
accumulates instead of extracting a span. -/
def parseString (s : String) (start : Pos) (acc : String) :
    Pos → Nat → Option (String × Pos)
  | _, 0 => none
  | i, fuel + 1 =>
    if h : i < s.rawEndPos then
      if byteAt s i h == '"'.toUInt8 then
        let rest := after i
        if hrest : rest < s.rawEndPos then
          if byteAt s rest hrest == '"'.toUInt8 then
            parseString s (after rest) (acc ++ span s start i ++ "\"") (after rest) fuel
          else
            some (acc ++ span s start i, rest)
        else
          some (acc ++ span s start i, rest)
      else
        parseString s start acc (after i) fuel
    else none

/-- End of an SMT-LIB `|…|`-quoted symbol body (the position of the closing `|`).
SMT-LIB does not define escapes inside quoted symbols, so a backslash is rejected. -/
def quotedSymbolEnd (s : String) : Pos → Nat → Option Pos
  | _, 0 => none
  | i, fuel + 1 =>
    if h : i < s.rawEndPos then
      let c := byteAt s i h
      if c == '|'.toUInt8 then some i
      else if c == '\\'.toUInt8 then none
      else quotedSymbolEnd s (after i) fuel
    else none

mutual
  /-- Parse one S-expression starting at `i`. Returns the value and the position
  just past it. -/
  def parseOne (s : String) (fuel : Nat) (i : Pos) : Option (Sexp × Pos) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let i := skipTrivia s i (fuel + 1)
      if h : i < s.rawEndPos then
        let c := byteAt s i h
        let rest := after i
        if c == '('.toUInt8 then
          match parseList s fuel #[] rest with
          | some (elems, close) => some (.list elems, close)
          | none => none
        else if c == ')'.toUInt8 then none
        else if c == '"'.toUInt8 then
          match parseString s rest "" rest (fuel + 1) with
          | some (str, close) => some (.str str, close)
          | none => none
        else if c == '|'.toUInt8 then
          match quotedSymbolEnd s rest (fuel + 1) with
          | some close => some (.atom (span s rest close), after close)
          | none => none
        else
          let close := atomEnd s i (fuel + 1)
          if close.byteIdx == i.byteIdx then none
          else some (.atom (span s i close), close)
      else none

  /-- Parse list elements until the matching `)`. -/
  def parseList (s : String) (fuel : Nat) (acc : Array Sexp) (i : Pos) :
      Option (Array Sexp × Pos) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let i := skipTrivia s i (fuel + 1)
      if h : i < s.rawEndPos then
        if byteAt s i h == ')'.toUInt8 then some (acc, after i)
        else
          match parseOne s fuel i with
          | some (e, rest) => parseList s fuel (acc.push e) rest
          | none => none
      else none
end

/-- Fuel sufficient for any scan of `s`: one unit per byte, plus one so an empty
input still gets a step. Every recursive step above consumes at least one byte. -/
def fuelFor (s : String) : Nat := s.utf8ByteSize + 1

end SexpParser

open SexpParser (Pos) in
/-- Parse a single S-expression starting at `i`, returning it and the position just
past it. `none` on malformed/empty input. -/
def parseSexpAt (s : String) (i : Pos) : Option (Sexp × Pos) :=
  SexpParser.parseOne s (SexpParser.fuelFor s) i

/-- Parse a single S-expression from the front of `s`, returning it and the
unconsumed remainder. `none` on malformed/empty input. -/
def parseSexp (s : String) : Option (Sexp × String) := do
  let (e, rest) ← parseSexpAt s 0
  return (e, String.Pos.Raw.extract s rest (String.rawEndPos s))

open SexpParser (Pos) in
/-- Parse every S-expression in `s` from `i` onwards. With `stopOnError`, malformed
remaining input ends the walk and keeps what parsed; otherwise it rejects the whole
parse.

The `rounds` bound makes this total, and a round that fails to advance is rejected. -/
private def parseSexpsFrom (s : String) (stopOnError : Bool) :
    Nat → Array Sexp → Pos → Option (Array Sexp)
  | 0, acc, i =>
    if (SexpParser.skipTrivia s i (SexpParser.fuelFor s)).byteIdx == s.rawEndPos.byteIdx
        || stopOnError then
      some acc
    else none
  | rounds + 1, acc, i =>
    let i := SexpParser.skipTrivia s i (SexpParser.fuelFor s)
    if i.byteIdx == s.rawEndPos.byteIdx then some acc
    else
      match parseSexpAt s i with
      | none => if stopOnError then some acc else none
      | some (e, rest) =>
        if i.byteIdx < rest.byteIdx then
          parseSexpsFrom s stopOnError rounds (acc.push e) rest
        else
          if stopOnError then some acc else none

/-- Parse every S-expression in `s` (e.g. a solver dumps several in a row).
Failure with non-trivia input rejects the entire parse instead of silently
returning a valid-looking prefix. -/
def parseSexps (s : String) : Array Sexp :=
  (parseSexpsFrom s (stopOnError := false) (SexpParser.fuelFor s) #[] 0).getD #[]

/-- Parse the longest prefix of `s` that consists of complete S-expressions,
discarding a malformed or truncated tail.

For solver output, where a killed or `--tlimit`-cut solver leaves a partial trailing
term after a usable core and certificate. -/
def parseSexpPrefix (s : String) : Array Sexp :=
  (parseSexpsFrom s (stopOnError := true) (SexpParser.fuelFor s) #[] 0).getD #[]

end Crush.SMT
