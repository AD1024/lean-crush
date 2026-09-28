import Crush

open Crush

namespace CPCFallbackTests

def divisibleByFive (x : Int) : Prop := x % 5 = 0

register_lowering term <<
  (divisibleByFive (term x)) => .app (.indexed "divisible" #[.inr 5]) #[x]
>>

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"

-- No inverse handler for `divisible` is registered. Both certificate formats
-- must use the core fallback, whose Lean proof uses the original definition.
/-- [crush.result] reconstruction succeeded; no axiom used -/
#guard_msgs(trace, substring := true) in
set_option trace.crush.result true in
set_option crush.reconstruct "alethe" in
theorem aletheCoreFallback (x : Int) (h : divisibleByFive x) : ¬x % 5 ≠ 0 := by
  crush using (simp_all [divisibleByFive])

/-- [crush.result] reconstruction succeeded; no axiom used -/
#guard_msgs(trace, substring := true) in
set_option trace.crush.result true in
set_option crush.reconstruct "cpc" in
theorem cpcCoreFallback (x : Int) (h : divisibleByFive x) : ¬x % 5 ≠ 0 := by
  crush using (simp_all [divisibleByFive])

/-- error: crush: CPC replay failed with term-gap -/
#guard_msgs(error, substring := true) in
set_option crush.reconstruct "cpc" in
set_option crush.reconstruct.fallback false in
example (x : Int) (h : divisibleByFive x) : ¬x % 5 ≠ 0 := by crush

-- Requiring replay remains strict even when the trust policy would otherwise
-- permit a warned trusted fallback.
/-- error: crush: CPC replay failed with term-gap -/
#guard_msgs(error, substring := true) in
set_option crush.trust "reconstructOrTrust" in
set_option crush.reconstruct "cpc" in
set_option crush.reconstruct.fallback false in
example (x : Int) (h : divisibleByFive x) : ¬x % 5 ≠ 0 := by crush

#eval show Lean.CoreM Unit from do
  for name in [``aletheCoreFallback, ``cpcCoreFallback] do
    let axioms ← Lean.collectAxioms name
    if axioms.contains ``Crush.crushSorry || axioms.contains ``sorryAx then
      throwError "core fallback escaped checked reconstruction"

-- Neither replay nor its core fallback may use an omitted contradictory fact.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
set_option crush.reconstruct "cpc" in
example (x : Int) (h0 : x = 0) (h1 : x = 1) : x = x + 1 := by crush []

end CPCFallbackTests
