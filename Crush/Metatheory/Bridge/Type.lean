import Lean
import Crush.Metatheory.HO.Core
import Crush.Metatheory.FO.Core

/-!
# Executable type-refinement bridge

`TypeBridge` retains the original normalized Lean type while assigning it a type
in the verified nondependent core.  Arrow flattening is then performed by a pure,
total function whose result is proved to agree with `FO.flattenArrow`.

Non-arrow Lean types are opaque bases, except `Prop`, which is the core Boolean
formula sort.  A dependent function is therefore opaque rather than falsely
represented as a nondependent arrow; this matches production's refusal to send
dependent arrows through `declareArrowSort`.
-/

namespace Crush.Metatheory.Bridge

open Lean Meta

/-- A normalized Lean type paired structurally with its verified core image. -/
inductive TypeBridge where
  | bool (expr : Expr)
  | base (expr : Expr) (sort : BaseSort)
  | arrow (expr : Expr) (domain codomain : TypeBridge)
  deriving Repr

namespace TypeBridge

def expr : TypeBridge → Expr
  | .bool expr | .base expr _ | .arrow expr _ _ => expr

def ty : TypeBridge → Ty
  | .bool _ => .bool
  | .base _ sort => .base sort
  | .arrow _ domain codomain => .arrow domain.ty codomain.ty

/-- Pure flattening of a reified nondependent arrow telescope. -/
def flatten : TypeBridge → List TypeBridge × TypeBridge
  | bridge@(.bool _) | bridge@(.base _ _) => ([], bridge)
  | .arrow _ domain codomain =>
      let (arguments, result) := codomain.flatten
      (domain :: arguments, result)

@[simp] theorem flatten_types (bridge : TypeBridge) :
    bridge.flatten.1.map TypeBridge.ty = (FO.flattenArrow bridge.ty).1 := by
  induction bridge with
  | bool | base => rfl
  | arrow expr domain codomain domainIH codomainIH =>
      simp only [flatten, ty, FO.flattenArrow, List.map_cons]
      rw [codomainIH]

@[simp] theorem flatten_result (bridge : TypeBridge) :
    bridge.flatten.2.ty = (FO.flattenArrow bridge.ty).2 := by
  induction bridge with
  | bool | base => rfl
  | arrow expr domain codomain domainIH codomainIH =>
      simp only [flatten, ty, FO.flattenArrow]
      exact codomainIH

end TypeBridge

/-- Evidence retained by the executable translator that a normalized Lean type
is represented by a genuine nondependent arrow in the verified core. -/
structure ArrowBridge where
  expr : Expr
  domain : TypeBridge
  codomain : TypeBridge
  deriving Repr

namespace ArrowBridge

def typeBridge (bridge : ArrowBridge) : TypeBridge :=
  .arrow bridge.expr bridge.domain bridge.codomain

def ty (bridge : ArrowBridge) : Ty :=
  .arrow bridge.domain.ty bridge.codomain.ty

/-- The same full application telescope consumed by production. -/
def flatten (bridge : ArrowBridge) : List TypeBridge × TypeBridge :=
  bridge.typeBridge.flatten

/-- The theorem-facing declaration represented by production's generated
`app` symbol for this arrow. -/
def appDecl (bridge : ArrowBridge) : FO.SymbolDecl :=
  FO.appDecl bridge.domain.ty bridge.codomain.ty

@[simp] theorem flatten_types (bridge : ArrowBridge) :
    bridge.flatten.1.map TypeBridge.ty = (FO.flattenArrow bridge.ty).1 :=
  TypeBridge.flatten_types bridge.typeBridge

@[simp] theorem flatten_result (bridge : ArrowBridge) :
    bridge.flatten.2.ty = (FO.flattenArrow bridge.ty).2 :=
  TypeBridge.flatten_result bridge.typeBridge

@[simp] theorem appDecl_args (bridge : ArrowBridge) :
    bridge.appDecl.args =
      FO.arrowSort bridge.domain.ty bridge.codomain.ty ::
        bridge.flatten.1.map (FO.FOSort.ofTy ∘ TypeBridge.ty) := by
  rw [appDecl, FO.appDecl_args]
  have telescope :
      bridge.domain.ty :: (FO.flattenArrow bridge.codomain.ty).1 =
        bridge.flatten.1.map TypeBridge.ty := by
    simp [ty]
  rw [telescope]
  have mapped :
      List.map FO.FOSort.ofTy (List.map TypeBridge.ty bridge.flatten.1) =
        List.map (FO.FOSort.ofTy ∘ TypeBridge.ty) bridge.flatten.1 :=
    List.map_map
  exact congrArg
    (fun arguments => FO.arrowSort bridge.domain.ty bridge.codomain.ty :: arguments)
    mapped

@[simp] theorem appDecl_result (bridge : ArrowBridge) :
    bridge.appDecl.result = FO.FOSort.ofTy bridge.flatten.2.ty := by
  rw [appDecl, FO.appDecl_result, bridge.flatten_result]
  rfl

end ArrowBridge

/-- Reify the fragment needed by production arrow-shape discovery.  Weak-head
normalization remains a metaprogramming boundary; after it returns, telescope
flattening is the proved total `TypeBridge.flatten` function. -/
partial def reifyType (type : Expr) (preserveExpr := false) : MetaM TypeBridge := do
  let normalized ← whnf type
  let liveExpr := if preserveExpr then type else normalized
  if normalized.isArrow then
    let .forallE _ domain codomain _ := normalized
      | throwError "crush: internal — `isArrow` without a forall expression"
    -- Production preserves each binder domain expression as it appeared after
    -- exposing the surrounding arrow, but weak-head normalizes the evolving
    -- codomain before deciding whether to continue flattening.
    return .arrow liveExpr
      (← reifyType domain (preserveExpr := true))
      (← reifyType codomain)
  if normalized == .sort .zero then
    return .bool liveExpr
  let rendered := toString (← ppExpr normalized)
  return .base liveExpr ⟨rendered⟩

/-- Reify only a genuine outer nondependent arrow, as required by
`arrowShape?`. -/
partial def reifyArrow? (type : Expr) : MetaM (Option ArrowBridge) := do
  let type ← whnf type
  unless type.isArrow do return none
  let .forallE _ domain codomain _ := type
    | throwError "crush: internal — `isArrow` without a forall expression"
  return some {
    expr := type
    domain := ← reifyType domain (preserveExpr := true)
    codomain := ← reifyType codomain }

end Crush.Metatheory.Bridge
