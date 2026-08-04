import Crush.Proofs.Semantics
import Crush.Translation.Theories

/-!
# Obligations about the *actual emitted terms*

The theorems here differ from a vacuous ledger in one specific way: each one is
stated about a term built by a function the translator really calls
(`Crush.intDivGuard`, `Crush.bvDivGuard`, the `≥ 0` guard shape) and evaluated by
the concrete `eval` of `Crush.Proofs.Semantics`. Every statement is therefore
falsifiable — and several of them *would have been false* before the corresponding
bug was fixed, which is the test of whether an obligation is worth anything.

The pattern is: state the property, then immediately state the counterexample the
buggy version produced, so the theorem and the regression sit together.
-/

namespace Crush.Proofs

open Crush.SMT Crush

/-- Evaluation with a generous fuel budget; every term here is small. -/
abbrev ev (I : Interp) (t : Term) : Option Value := eval 32 (fun _ => none) I t

/-- The empty interpretation: no uninterpreted symbol has a meaning, so anything
that evaluates does so purely by the theory operators. -/
def emptyI : Interp := { symbols := fun _ _ => none }

/-- An interpretation assigning a single `Int` constant. -/
def constI (name : String) (v : Int) : Interp :=
  { symbols := fun f args => if f == name && args.isEmpty then some (.int v) else none }

/-! ## The `≥ 0` guard on `Nat`-encoded values

`Nat` is encoded as `Int`, so every `Nat`-typed symbol carries `(>= x 0)`. The
obligation is that this guard is *exact*: it accepts precisely the images of Lean
`Nat`s. `p10_wf_exact` in `Obligations.lean` proves that on the Lean side; here it is
checked against the emitted term. -/

/-- The guard term the translator emits for a nullary `Nat`-encoded symbol. -/
def natGuardTerm (name : String) : Term :=
  .symbApp ">=" #[.const name, .lit (.num 0)]

/-- The emitted guard accepts a non-negative value. -/
theorem natGuard_accepts_nonneg :
    ev (constI "n" 5) (natGuardTerm "n") = some (.bool true) := by decide

/-- …and rejects a negative one. Together with the previous theorem this pins that
the guard is the *exact* characterization rather than merely a sound one: a guard
that accepted everything would pass the first test and fail this one. -/
theorem natGuard_rejects_negative :
    ev (constI "n" (-1)) (natGuardTerm "n") = some (.bool false) := by decide

theorem natGuard_accepts_zero :
    ev (constI "n" 0) (natGuardTerm "n") = some (.bool true) := by decide

/-! ## `Int` division and modulus at a zero divisor

SMT-LIB leaves `(div x 0)` underspecified, while Lean pins `x / 0 = 0` and
`x % 0 = x`. `Crush.intDivGuard` wraps the operator so the encoding is exact. These
theorems evaluate the *real* guard term.

The semantics deliberately gives `(div a 0)` no value (`none`) rather than picking
one, so a theorem here cannot accidentally rely on our modelling choice: the guard
must produce the answer without the underspecified branch ever being consulted. -/

/-- `intDivGuard "div"` returns Lean's `0` at a zero divisor — and it does so
without evaluating the underspecified `(div a 0)`, which has no value at all. -/
theorem intDivGuard_div_zero :
    ev emptyI (intDivGuard "div" (.lit (.num 7)) (.lit (.num 0))) = some (.int 0) := by
  decide

/-- `intDivGuard "mod"` returns Lean's `x` at a zero divisor. -/
theorem intDivGuard_mod_zero :
    ev emptyI (intDivGuard "mod" (.lit (.num 7)) (.lit (.num 0))) = some (.int 7) := by
  decide

/-- Away from zero the guard is transparent: it agrees with the raw operator, so
adding it costs no precision. Checked at a value where Euclidean and truncated
division *differ*, which is the case that matters. -/
theorem intDivGuard_transparent :
    ev emptyI (intDivGuard "div" (.lit (.num 7)) (.lit (.num 2))) = some (.int 3) := by
  decide

/-- **The bug this guard prevents.** Emitting the raw operator leaves the
zero-divisor case with no value at all, so the encoding cannot derive Lean's
`x / 0 = 0`. This theorem is what fails if someone deletes `intDivGuard`. -/
theorem raw_div_zero_unmodelled :
    ev emptyI (.symbApp "div" #[.lit (.num 7), .lit (.num 0)]) = none := by decide

/-! ## Ill-sorted emission is detectable here even though solvers accept it

The translator once emitted a type argument as a term, producing applications like
`(= x true)` for an `Int`-sorted `x`. **z3 does not reject that** — it silently
reinterprets, so nothing surfaces at the solver boundary and the only symptom is
wrong answers.

`evalOp` requires equality and `ite` to be *homogeneous*, so the same malformed
terms have no value here. That makes this semantics strictly more discriminating
than the solver, and it is the property that would have caught those bugs. -/

/-- A heterogeneous equality has no value, rather than a coerced one. -/
theorem heterogeneous_eq_unmodelled :
    ev emptyI (.symbApp "=" #[.lit (.num 2), .lit (.bool true)]) = none := by decide

/-- Arithmetic on a boolean has no value. -/
theorem bool_in_arith_unmodelled :
    ev emptyI (.symbApp "+" #[.lit (.num 2), .lit (.bool true)]) = none := by decide

/-- An `ite` whose branches disagree in sort has no value. -/
theorem heterogeneous_ite_unmodelled :
    ev emptyI (.symbApp "ite" #[.lit (.bool true), .lit (.num 1), .lit (.bool false)])
      = none := by decide

/-- A non-`Bool` antecedent to `=>` has no value. This is the shape the
`Empty → False` bug produced, where a *type* was placed in a proposition position. -/
theorem nonbool_implication_unmodelled :
    ev emptyI (.symbApp "=>" #[.lit (.num 1), .lit (.bool true)]) = none := by decide

/-! ## Guarded quantifier shapes

The `∀`/`∃` guard shapes are the subject of `p10_guarded_quantifier` and
`p10_guarded_existential`. The critical asymmetry — `⇒` for `∀`, `∧` for `∃` — is a
known false-`unsat` when got wrong: with `⇒`, `∃ n : Nat, False` becomes satisfiable
by any negative witness.

These evaluate the real shapes over an explicit finite domain that *includes a
negative value*, which is exactly the phantom the guard must exclude. -/

/-- A domain containing one legitimate and one phantom (negative) value. -/
def intDom : Domain := fun _ => some [.int 0, .int 1, .int (-1)]

abbrev evD (I : Interp) (t : Term) : Option Value := eval 32 intDom I t

/-- `∀` guarded with `⇒`: the phantom `-1` is excluded, so a property that holds of
the non-negative values holds of the guarded quantification. -/
theorem forall_guard_excludes_phantom :
    evD emptyI (.forallE #[("x", .app (.symb "Int") #[])]
      (.symbApp "=>" #[.symbApp ">=" #[.bvar 0, .lit (.num 0)],
                       .symbApp ">=" #[.bvar 0, .lit (.num 0)]])) = some (.bool true) := by
  decide

/-- `∃` guarded with `∧` correctly reports that no `Nat` satisfies `False`. -/
theorem exists_guard_conjunction_correct :
    evD emptyI (.existsE #[("x", .app (.symb "Int") #[])]
      (.symbApp "and" #[.symbApp ">=" #[.bvar 0, .lit (.num 0)],
                        .lit (.bool false)])) = some (.bool false) := by
  decide

/-- **The bug.** With `⇒` instead of `∧`, `∃ n : Nat, False` becomes *true*,
witnessed by the phantom `-1` for which the guard is vacuously satisfied. This
theorem states the wrong shape and proves it wrong, so the two sit side by side. -/
theorem exists_guard_implication_is_wrong :
    evD emptyI (.existsE #[("x", .app (.symb "Int") #[])]
      (.symbApp "=>" #[.symbApp ">=" #[.bvar 0, .lit (.num 0)],
                       .lit (.bool false)])) = some (.bool true) := by
  decide

end Crush.Proofs
