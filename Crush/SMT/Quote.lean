import Lean
import Crush.SMT.Print

/-!
# SMT-LIB term quotations

`(smt| ...)` is a shallow embedding of the first-order SMT-LIB term syntax into
`Crush.SMT.Term`. It supports symbols, applications, natural-number, Boolean, and
string literals, plus `$term` splices for existing `SMT.Term` values:

```lean
let x : SMT.Term := .const "x"
let t : SMT.Term := (smt| (ite (> $x 0) 1 (- 1)))
```

The quotation expands to ordinary `SMT.Term` constructors at compile time. It does
not parse or retain an untyped SMT string.
-/

namespace Crush.SMT

namespace Parser

open Lean
open Lean.Parser

/-- Syntax-node kind used for an SMT-LIB simple symbol. -/
abbrev symbolKind : SyntaxNodeKind := `Crush.SMT.Parser.symbol

/-- Parse an SMT-LIB simple symbol independently of Lean's identifier grammar. -/
def symbolFn : ParserFn := fun c s =>
  let start := s.pos
  let s := satisfyFn isInitialSimpleSymbolChar "SMT-LIB symbol" c s
  if s.hasError then
    s
  else
    let s := takeWhileFn isSimpleSymbolChar c s
    mkNodeToken symbolKind start true c s

/-- Parser for SMT-LIB simple symbols such as `ite`, `str.++`, `=>`, and `>=`. -/
def symbol : Lean.Parser.Parser := {
  fn := symbolFn
  info := mkAtomicInfo "SMT-LIB symbol"
}

end Parser

end Crush.SMT

namespace Lean.PrettyPrinter

open Formatter Parenthesizer

@[combinator_formatter Crush.SMT.Parser.symbol]
def smtSymbolFormatter := visitAtom Crush.SMT.Parser.symbolKind

@[combinator_parenthesizer Crush.SMT.Parser.symbol]
def smtSymbolParenthesizer := visitToken

end Lean.PrettyPrinter

namespace Crush.SMT

declare_syntax_cat smtTerm

syntax (name := smtNumeral) num : smtTerm
syntax (name := smtString) str : smtTerm
syntax (name := smtIdent) ident : smtTerm
syntax (name := smtSymbol) Parser.symbol : smtTerm
syntax (name := smtApp) "(" Parser.symbol smtTerm* ")" : smtTerm

/-- Shallow SMT-LIB term quotation. Use `$t` to splice a Lean expression of type
`SMT.Term`. -/
syntax (name := smtQuot) "(smt|" smtTerm ")" : term

open Lean Macro

private def symbolString (stx : Syntax) : MacroM String :=
  match stx.getArgs.back? with
  | some (.atom _ value) => return value
  | _ => Macro.throwErrorAt stx "invalid SMT-LIB symbol"

private partial def expandTerm (stx : Syntax) : MacroM Syntax := do
  if stx.isAntiquot then
    return stx.getAntiquotTerm
  else if stx.isOfKind ``smtNumeral then
    let some numeral := stx[0].isNatLit?
      | Macro.throwErrorAt stx "invalid SMT-LIB numeral"
    `(SMT.Term.lit (.num $(quote numeral)))
  else if stx.isOfKind ``smtString then
    let some string := stx[0].isStrLit?
      | Macro.throwErrorAt stx "invalid SMT-LIB string literal"
    `(SMT.Term.lit (.str $(quote string)))
  else if stx.isOfKind ``smtIdent then
    let value := stx[0].getId.toString
    match value with
    | "true" => `(SMT.Term.lit (.bool true))
    | "false" => `(SMT.Term.lit (.bool false))
    | _ => `(SMT.Term.const $(Syntax.mkStrLit value))
  else if stx.isOfKind ``smtSymbol then
      let value ← symbolString stx[0]
      `(SMT.Term.const $(Syntax.mkStrLit value))
  else if stx.isOfKind ``smtApp then
      let value ← symbolString stx[1]
      let args : Array (TSyntax `term) :=
        (← stx[2].getArgs.mapM expandTerm).map (⟨·⟩)
      `(SMT.Term.symbApp $(Syntax.mkStrLit value) #[$[$args],*])
  else
    Macro.throwErrorAt stx s!"unsupported SMT-LIB term syntax ({stx.getKind}): {stx}"

macro_rules
  | `(term| (smt| $term:smtTerm)) => expandTerm term

end Crush.SMT
