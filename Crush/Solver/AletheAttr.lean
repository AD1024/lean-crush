import Lean
import Crush.SMT.Sexp

open Lean Elab Meta

/-!
# Extensible Alethe term decoding

Custom SMT lowerings can introduce theory operators that the built-in Alethe term
decoder does not know. `@[crush_alethe "operator"]` registers the inverse mapping
needed by checked certificate replay.
-/

namespace Crush

open SMT

/-- A decoded SMT application offered to a user Alethe decoder. -/
structure AletheDecoderContext where
  /-- The ordinary or indexed SMT operator name. -/
  head : String
  /-- Indexed-identifier payload, excluding `_` and the operator name. -/
  indices : Array Sexp
  /-- Recursively decoded Lean arguments. -/
  args : Array Expr

/-- Reconstruct the Lean expression denoted by an SMT operator application.

Returning `none` defers to the next decoder. Built-in theory decoding runs before
registered handlers. -/
abbrev AletheDecoder := AletheDecoderContext → MetaM (Option Expr)

instance : TypeName AletheDecoder := unsafe (TypeName.mk _ ``AletheDecoder)

/-- Serializable metadata for one operator-indexed decoder. -/
private structure DecoderEntry where
  head : String
  declName : Name
  priority : Nat
  deriving Inhabited

private structure DecoderDecl where
  declName : Name
  priority : Nat
  deriving Inhabited

private abbrev DecoderState := Std.HashMap String (Array DecoderDecl)

private def addDecoderEntry (state : DecoderState) (entry : DecoderEntry) : DecoderState :=
  state.alter entry.head fun entries =>
    (entries.getD #[]).push { declName := entry.declName, priority := entry.priority }

initialize crushAletheDecoderExt :
    SimplePersistentEnvExtension DecoderEntry DecoderState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addDecoderEntry
    addImportedFn := fun imports =>
      imports.foldl (init := {}) fun state entries =>
        entries.foldl (init := state) addDecoderEntry
  }

/-- Register an inverse decoder for one SMT operator.

Higher priorities run first. A handler is consulted only when built-in decoding
does not recognize the application. -/
syntax (name := crushAletheAttr) "crush_alethe " str (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `crushAletheAttr
  descr := "Register an operator-indexed lean-crush Alethe term decoder."
  applicationTime := .afterCompilation
  add := fun declName stx _ => do
    let some head := stx[1].isStrLit?
      | throwError "@[crush_alethe] expects an SMT operator string"
    let priority ← getAttrParamOptPrio stx[2]
    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration {declName}"
    let expectedType := mkConst ``Crush.AletheDecoder
    unless (← MetaM.run' (withoutModifyingState <|
        Meta.isDefEqGuarded info.type expectedType)) do
      throwError "@[crush_alethe] expects a declaration of type `AletheDecoder`, \
                  but {declName} has type{indentExpr info.type}"
    modifyEnv fun env =>
      crushAletheDecoderExt.addEntry env { head, declName, priority }
}

/-- Resolved Alethe decoders, grouped by SMT operator and ordered by priority. -/
abbrev AletheDecoderRegistry := Std.HashMap String (Array AletheDecoder)

unsafe def getAletheDecodersUnsafe : MetaM AletheDecoderRegistry := do
  let env ← getEnv
  let options ← getOptions
  let mut result : AletheDecoderRegistry := {}
  for (head, entries) in (crushAletheDecoderExt.getState env).toList do
    let names :=
      (entries.qsort fun left right => left.priority > right.priority).map (·.declName)
    let handlers ← names.filterMapM fun declName => do
      match env.evalConst AletheDecoder options declName with
      | .ok handler => return some handler
      | .error error =>
        throwError "failed to evaluate Alethe decoder `{declName}`: {error}"
    result := result.insert head handlers
  return result

@[implemented_by getAletheDecodersUnsafe]
opaque getAletheDecoders : MetaM AletheDecoderRegistry

/-- Whether an operator has any registered inverse decoders. -/
def hasAletheDecodersFor (head : String) : CoreM Bool := do
  return (crushAletheDecoderExt.getState (← getEnv)).contains head

/-- Run registered decoders for an application after the built-in decoder declines. -/
def runAletheDecoders (registry : AletheDecoderRegistry)
    (head : String) (indices : Array Sexp) (args : Array Expr) :
    MetaM (Option Expr) := do
  for decoder in registry.getD head #[] do
    if let some result ← decoder { head, indices, args } then
      let result ← instantiateMVars result
      let _ ← inferType result
      return some result
  return none

end Crush
