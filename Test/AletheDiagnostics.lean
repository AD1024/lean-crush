import Crush

/-!
Regression tests for actionable Alethe replay failures.
-/

open Crush Crush.SMT

def MultipleOfFive (value : Int) : Prop :=
  value % 5 = 0

@[crush_lower MultipleOfFive]
def lowerMultipleOfFive : LoweringHandler := fun ctx => do
  let #[value] := ctx.args | return none
  return some (.app (.indexed "divisible" #[.inr 5]) #[← ctx.emitTerm value])

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option crush.timeout 10

/-!
No `@[crush_alethe "divisible"]` decoder is registered in this module. The solver
still emits a certificate, but replay must reject the source assumption containing
the custom operator before any derived step can use it.
-/

/--
error: crush: Alethe replay failed with term-gap at step `crush_fact_0`
-/
#guard_msgs(error, substring := true) in
example (x : Int) (hx : MultipleOfFive x) :
    ¬x % 5 ≠ 0 := by
  crush
