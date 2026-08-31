import Crush.Metatheory.Reification.Reify

/-!
# Explicit trusted and proved boundary evidence

The executable translator remains extensible, so not every path has a semantic
proof.  These types make that distinction structural rather than encoding it as
an absent optional witness.
-/

namespace Crush.Metatheory.VCG

open Crush.Metatheory.Reification

open Lean

/-- Why one executable translation step lies outside the proved fragment. -/
inductive TrustReason where
  | direct (source : Expr)
  | termHandler (source : Expr)
  | sortHandler (source : Expr)
  | lowering (head : Name)
  | resultLowering (head : Name)
  | closure (source : Expr)
  | constant (source : Expr)
  | nativeHO (source : Expr)
  | datatype (reason : DatatypeReject)
  | unsupported (source : Expr)
  deriving Inhabited, Repr

/-- A closure equation either retains its typed reification/capture proof or
records why it crossed the trusted boundary. -/
inductive ClosureEvidence where
  | proved (certificate : SomeCertifiedClosure)
  | trusted (reason : TrustReason)

end Crush.Metatheory.VCG
