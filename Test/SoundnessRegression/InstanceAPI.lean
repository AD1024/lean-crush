import Crush

/-!
Custom operator lowerings compare against an explicit dictionary. Local and global
overrides must not change that baseline. The legacy built-in-only helper advertises
its restriction at the call site.
-/

open Lean Meta Crush

namespace SoundnessInstanceAPI

class MyAdd (α : Type) where
  op : α → α → α

instance myAddInt : MyAdd Int := ⟨(· + ·)⟩

@[crush_lower MyAdd.op]
def lowerMyAdd : LoweringHandler := fun ctx => do
  let #[α, _, x, y] := ctx.args | return none
  unless ← isDefEqRigid α (mkConst ``Int) do return none
  unless ← ctx.hasExpectedInstance 1 (mkConst ``myAddInt) do return none
  return some (smt| (+ $(← ctx.emitTerm x) $(← ctx.emitTerm y)))

example (x y : Int) : MyAdd.op x y = MyAdd.op y x := by crush

@[instance_reducible]
def subtractMyAdd : MyAdd Int := ⟨(· - ·)⟩

run_meta do
  for dictionary in #[``myAddInt, ``subtractMyAdd] do
    let expression := mkAppN (mkConst ``MyAdd.op)
      #[mkConst ``Int, mkConst dictionary, mkIntLit 2, mkIntLit 3]
    let (term, _) ← TranslateM.run {} (emitTerm expression)
    unless (toString term == "(+ 2 3)") == (dictionary == ``myAddInt) do
      throwError "custom lowering did not respect its exact instance dictionary"

section
local instance (priority := high) : MyAdd Int := subtractMyAdd

/-- error: crush: could not prove the goal — the solver found a model -/
#guard_msgs(error, substring := true) in
example (x y : Int) : MyAdd.op x y = MyAdd.op y x := by crush
end

instance (priority := high) globalOverride : MyAdd Int := subtractMyAdd

/-- error: crush: could not prove the goal — the solver found a model -/
#guard_msgs(error, substring := true) in
example (x y : Int) : MyAdd.op x y = MyAdd.op y x := by crush

/-- warning: `Crush.TranslationCtx.hasCanonicalInstance` has been deprecated: Use `hasExpectedInstance` with the exact dictionary your lowering implements -/
#guard_msgs(warning, substring := true) in
def legacyCheck (ctx : TranslationCtx) : TranslateM Bool :=
  ctx.hasCanonicalInstance 1

end SoundnessInstanceAPI
