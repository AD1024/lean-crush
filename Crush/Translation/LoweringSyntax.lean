import Crush.Translation.Attr
import Crush.SMT.Quote

open Lean Elab Command

/-!
# Pattern-based lowering registrations

`register_lowering term`, `result-type`, and `sort` compile to private definitions
registered through the existing lowering attributes. Patterns inspect complete
elaborated application spines without unfolding. Matching finishes before any
capture is translated, so a declined pattern emits no declarations.
An optional `with ctx` explicitly binds the original `TranslationCtx` for the RHS.
-/

namespace Crush

declare_syntax_cat crushLoweringPattern
declare_syntax_cat crushLoweringKind

namespace LoweringParser

def termKeyword : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "term" (includeIdent := true)
def sortKeyword : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "sort" (includeIdent := true)
def fencedRhs : Lean.Parser.Parser :=
  Lean.Parser.withForbidden ">>" Lean.Parser.termParser

end LoweringParser

syntax LoweringParser.termKeyword : crushLoweringKind
syntax "result-type" : crushLoweringKind
syntax LoweringParser.sortKeyword : crushLoweringKind

syntax "_" : crushLoweringPattern
syntax ident : crushLoweringPattern
syntax "(" ident crushLoweringPattern* ")" : crushLoweringPattern
syntax (priority := high) "(" LoweringParser.termKeyword ident
  (" : " crushLoweringPattern)? ")" : crushLoweringPattern
syntax (priority := high) "(" LoweringParser.sortKeyword ident ")" : crushLoweringPattern

/-- Register a structural Lean pattern with an SMT term or sort template. -/
syntax (name := registerLowering)
  "register_lowering" ppSpace crushLoweringKind (ppSpace prio)?
  (ppSpace "with " ident)? ppSpace
  "<<" ppLine crushLoweringPattern ppSpace "=>" ppSpace
  LoweringParser.fencedRhs ppLine ">>" : command

private inductive CaptureKind where
  | term | sort | expr

private structure LoweringCapture where
  name : Ident
  value : Ident
  kind : CaptureKind

private structure PatternCode where
  checks : Array (TSyntax `doElem) := #[]
  captures : Array LoweringCapture := #[]

private def freshIdent : CommandElabM Ident :=
  liftMacroM <| withFreshMacroScope `(loweringValue)

private def patternHead (pattern : TSyntax `crushLoweringPattern) :
    CommandElabM Ident := do
  match pattern with
  | `(crushLoweringPattern| $head:ident) => return head
  | `(crushLoweringPattern| ($head:ident $_:crushLoweringPattern*)) => return head
  | _ => throwErrorAt pattern "a lowering pattern must have a constant application head"

private partial def compilePattern (pattern : TSyntax `crushLoweringPattern)
    (value : Ident) (code : PatternCode := {}) (headOnly := false) : CommandElabM PatternCode := do
  match pattern with
  | `(crushLoweringPattern| _) => return code
  | `(crushLoweringPattern| (term $name:ident $[: $type:crushLoweringPattern]?)) =>
    let code ← addCapture code name .term
    if let some type := type then
      let typeValue ← freshIdent
      let check ← `(doElem| let $typeValue ← Lean.Meta.inferType $value)
      compilePattern type typeValue { code with checks := code.checks.push check } true
    else return code
  | `(crushLoweringPattern| (sort $name:ident)) =>
    let check ← `(doElem|
      unless (← Lean.Meta.whnf (← Lean.Meta.inferType $value)).isSort do return none)
    addCapture { code with checks := code.checks.push check } name .sort
  | `(crushLoweringPattern| $head:ident) =>
    if headOnly then application code head #[] else addCapture code head .expr
  | `(crushLoweringPattern| ($head:ident $args:crushLoweringPattern*)) =>
    application code head args
  | _ => throwErrorAt pattern "unsupported lowering pattern"
where
  addCapture (code : PatternCode) (name : Ident) (kind : CaptureKind) :
      CommandElabM PatternCode := do
    if code.captures.any (·.name.getId == name.getId) then
      throwErrorAt name "duplicate lowering capture `{name}`; each capture must occur once"
    return { code with captures := code.captures.push { name, value, kind } }
  application (code : PatternCode) (head : Ident)
      (args : Array (TSyntax `crushLoweringPattern)) : CommandElabM PatternCode := do
    let headName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo head
    let expression ← freshIdent
    let spine ← freshIdent
    let mut code := { code with checks := code.checks ++ #[
      (← `(doElem| let $expression := Lean.Expr.consumeMData $value)),
      (← `(doElem| unless ($expression).getAppFn.isConstOf $(quote headName) do return none)),
      (← `(doElem| let $spine := ($expression).getAppArgs)),
      (← `(doElem| unless ($spine).size == $(quote args.size) do return none))] }
    for i in [:args.size] do
      let arg ← freshIdent
      let check ← `(doElem| let $arg := $spine[$(quote i)]!)
      code := { code with checks := code.checks.push check }
      code ← compilePattern args[i]! arg code
    return code

/-- Internal elaboration adapter: prefer a monadic RHS, otherwise lift a pure value. -/
syntax (name := loweringRhs) "lowering_rhs% " term : term

@[term_elab loweringRhs]
def elabLoweringRhs : Term.TermElab := fun stx expectedType? => do
  let rhs : TSyntax `term := ⟨stx[1]⟩
  -- Keep the existing handler return type available for helpers that may decline.
  let candidates := #[rhs, (← `(term| some <$> $rhs)), (← `(term| pure (some $rhs)))]
  for candidate in candidates[:2] do
    let result ← Term.observing <| Term.withoutErrToSorry <|
      Term.elabTermEnsuringType candidate expectedType?
    if let .ok .. := result then return ← Term.applyResult result
  Term.elabTermEnsuringType candidates[2]! expectedType?

elab_rules : command
  | `(register_lowering $kind:crushLoweringKind $[$priority:prio]?
      $[with $contextName:ident]?
      << $pattern:crushLoweringPattern => $rhs:term >>) => do
    let head ← patternHead pattern
    let headName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo head
    let head := mkIdentFrom head headName
    let ctx ← match contextName with
      | some name => pure name
      | none => freshIdent
    let value ← freshIdent
    let name ← freshIdent
    let code ← compilePattern pattern value (headOnly := true)
    if let some contextName := contextName then
      if code.captures.any (·.name.getId == contextName.getId) then
        throwErrorAt contextName
          "lowering context binder `{contextName}` conflicts with a pattern capture"
    let mut bindings : Array (TSyntax `doElem) := #[]
    for capture in code.captures do
      let captureName := capture.name
      let captureValue := capture.value
      let binding ← match capture.kind with
        | .term => `(doElem| let $captureName ← ($ctx).emitTerm $captureValue)
        | .sort => `(doElem| let $captureName ← ($ctx).emitSort $captureValue)
        | .expr => `(doElem| let $captureName := $captureValue)
      bindings := bindings.push binding
    let attrStx ← match kind with
      | `(crushLoweringKind| term) => `(attr| crush_lower $head $[$priority]?)
      | `(crushLoweringKind| result-type) => `(attr| crush_lower_result $head $[$priority]?)
      | `(crushLoweringKind| sort) => `(attr| crush_translate_sort $[$priority]?)
      | _ => throwUnsupportedSyntax
    let resultType ← match kind with
      | `(crushLoweringKind| sort) => `(SortHandler)
      | _ => `(LoweringHandler)
    let input ← match kind with
      | `(crushLoweringKind| result-type) =>
        `(doElem| let $value ← Lean.Meta.inferType (Lean.mkAppN ($ctx).fn ($ctx).args))
      | _ => `(doElem| let $value := Lean.mkAppN ($ctx).fn ($ctx).args)
    let checks := code.checks
    elabCommand (← `(command|
      @[$attrStx:attr] private def $name : $resultType := fun $ctx => do
        $input:doElem
        $[$checks:doElem]*
        $[$bindings:doElem]*
        lowering_rhs% $rhs))

end Crush
