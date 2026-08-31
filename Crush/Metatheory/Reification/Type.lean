import Lean
import Crush.Metatheory.HO.Core
import Crush.Metatheory.FO.Core

/-!
# Executable type reification

`ReifiedType` retains the Lean type expression selected by the translator while
assigning it a type in the verified nondependent core. Arrow flattening is then
performed by a pure, total function whose result is proved to agree with
`FO.flattenArrow`.

Non-arrow Lean types are opaque bases, except `Prop`, which is the core Boolean
formula sort.  A dependent function is therefore opaque rather than falsely
represented as a nondependent arrow; this matches the Crush translator's refusal to send
dependent arrows through `declareArrowSort`.
-/

namespace Crush.Metatheory.Reification

open Lean Meta

/-- A normalized Lean type paired structurally with its verified core image. -/
inductive ReifiedType where
  | bool (expr : Expr)
  | base (expr : Expr) (sort : BaseSort)
  | arrow (expr : Expr) (domain codomain : ReifiedType)
  deriving Repr

namespace ReifiedType

def expr : ReifiedType → Expr
  | .bool expr | .base expr _ | .arrow expr _ _ => expr

def ty : ReifiedType → Ty
  | .bool _ => .bool
  | .base _ sort => .base sort
  | .arrow _ domain codomain => .arrow domain.ty codomain.ty

/-- Pure flattening of a reified nondependent arrow telescope. -/
def flatten : ReifiedType → List ReifiedType × ReifiedType
  | reified@(.bool _) | reified@(.base _ _) => ([], reified)
  | .arrow _ domain codomain =>
      let (arguments, result) := codomain.flatten
      (domain :: arguments, result)

@[simp] theorem flatten_types (reified : ReifiedType) :
    reified.flatten.1.map ReifiedType.ty = (FO.flattenArrow reified.ty).1 := by
  induction reified with
  | bool | base => rfl
  | arrow expr domain codomain domainIH codomainIH =>
      simp only [flatten, ty, FO.flattenArrow, List.map_cons]
      rw [codomainIH]

@[simp] theorem flatten_result (reified : ReifiedType) :
    reified.flatten.2.ty = (FO.flattenArrow reified.ty).2 := by
  induction reified with
  | bool | base => rfl
  | arrow expr domain codomain domainIH codomainIH =>
      simp only [flatten, ty, FO.flattenArrow]
      exact codomainIH

end ReifiedType

/-- Evidence retained by the executable translator that a normalized Lean type
is represented by a genuine nondependent arrow in the verified core. -/
structure ReifiedArrowType where
  expr : Expr
  domain : ReifiedType
  codomain : ReifiedType
  deriving Repr

namespace ReifiedArrowType

def reifiedType (reified : ReifiedArrowType) : ReifiedType :=
  .arrow reified.expr reified.domain reified.codomain

def ty (reified : ReifiedArrowType) : Ty :=
  .arrow reified.domain.ty reified.codomain.ty

/-- The same full application telescope consumed by the Crush translator. -/
def flatten (reified : ReifiedArrowType) : List ReifiedType × ReifiedType :=
  reified.reifiedType.flatten

/-- The theorem-facing declaration represented by the Crush translator's generated
`app` symbol for this arrow. -/
def appDecl (reified : ReifiedArrowType) : FO.SymbolDecl :=
  FO.appDecl reified.domain.ty reified.codomain.ty

@[simp] theorem flatten_types (reified : ReifiedArrowType) :
    reified.flatten.1.map ReifiedType.ty = (FO.flattenArrow reified.ty).1 :=
  ReifiedType.flatten_types reified.reifiedType

@[simp] theorem flatten_result (reified : ReifiedArrowType) :
    reified.flatten.2.ty = (FO.flattenArrow reified.ty).2 :=
  ReifiedType.flatten_result reified.reifiedType

@[simp] theorem appDecl_args (reified : ReifiedArrowType) :
    reified.appDecl.args =
      FO.arrowSort reified.domain.ty reified.codomain.ty ::
        reified.flatten.1.map (FO.FOSort.ofTy ∘ ReifiedType.ty) := by
  rw [appDecl, FO.appDecl_args]
  have telescope :
      reified.domain.ty :: (FO.flattenArrow reified.codomain.ty).1 =
        reified.flatten.1.map ReifiedType.ty := by
    simp [ty]
  rw [telescope]
  have mapped :
      List.map FO.FOSort.ofTy (List.map ReifiedType.ty reified.flatten.1) =
        List.map (FO.FOSort.ofTy ∘ ReifiedType.ty) reified.flatten.1 :=
    List.map_map
  exact congrArg
    (fun arguments => FO.arrowSort reified.domain.ty reified.codomain.ty :: arguments)
    mapped

@[simp] theorem appDecl_result (reified : ReifiedArrowType) :
    reified.appDecl.result = FO.FOSort.ofTy reified.flatten.2.ty := by
  rw [appDecl, FO.appDecl_result, reified.flatten_result]
  rfl

end ReifiedArrowType

/-- Reify the fragment needed by translator arrow-shape discovery.  Weak-head
normalization remains a metaprogramming boundary; after it returns, telescope
flattening is the proved total `ReifiedType.flatten` function. -/
partial def reifyType (type : Expr) (preserveExpr := false) : MetaM ReifiedType := do
  let normalized ← whnf type
  let retainedExpr := if preserveExpr then type else normalized
  if normalized.isArrow then
    let .forallE _ domain codomain _ := normalized
      | throwError "crush: internal — `isArrow` without a forall expression"
    -- The Crush translator preserves each binder domain expression as it appeared after
    -- exposing the surrounding arrow, but weak-head normalizes the evolving
    -- codomain before deciding whether to continue flattening.
    return .arrow retainedExpr
      (← reifyType domain (preserveExpr := true))
      (← reifyType codomain)
  if normalized == .sort .zero then
    return .bool retainedExpr
  let rendered := toString (← ppExpr normalized)
  return .base retainedExpr ⟨rendered⟩

/-- Reify only a genuine outer nondependent arrow, as required by
`arrowShape?`. -/
partial def reifyArrow? (type : Expr) : MetaM (Option ReifiedArrowType) := do
  let type ← whnf type
  unless type.isArrow do return none
  let .forallE _ domain codomain _ := type
    | throwError "crush: internal — `isArrow` without a forall expression"
  return some {
    expr := type
    domain := ← reifyType domain (preserveExpr := true)
    codomain := ← reifyType codomain }

end Crush.Metatheory.Reification
