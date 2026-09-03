import Crush.Metatheory.HO.Core
import Crush.Metatheory.FO.Core

/-!
# Shared syntax for defunctionalization

The higher-order source context is erased pointwise to the first-order target
context.  This small interface is shared by closure capture and flattened
translation; it is independent of any particular defunctionalization encoding.
-/

namespace Crush.Metatheory.Defunctionalization

/-- Erasure of a higher-order source context to first-order target sorts. -/
@[reducible] def targetContext (context : Context) : FO.Context :=
  context.map FO.FOSort.ofTy

/-- A typed source variable at the corresponding position in the erased context. -/
def targetVar {context : Context} {ty : Ty} (ref : Var context ty) :
    FO.Var (targetContext context) (FO.FOSort.ofTy ty) :=
  match ref with
  | .here => .here
  | .there ref => .there (targetVar ref)

@[simp] theorem targetContext_cons (head : Ty) (tail : Context) :
    targetContext (head :: tail) = FO.FOSort.ofTy head :: targetContext tail := rfl

end Crush.Metatheory.Defunctionalization
