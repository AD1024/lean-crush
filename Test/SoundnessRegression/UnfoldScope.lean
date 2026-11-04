import Crush.Translation.Unfold

/-!
Automatic unfolding metadata must follow local, global, and scoped attributes,
including erasure and restoration at section boundaries. Equation collection must
reflect the currently active attributes.
-/

open Lean Meta Crush

private def checkUnfoldKind (name : Name) (expected : Option UnfoldKind) : MetaM Unit := do
  unless (crushUnfoldExt.getState (← getEnv)).get? name == expected do
    throwError "unexpected automatic-unfold attribute state for {name}"
  let lemmas ← relevantAutoUnfoldLemmas #[name]
  unless lemmas.isEmpty == expected.isNone do
    throwError "automatic-unfold equations do not reflect the active attribute for {name}"

def localUnfold (n : Nat) := n + 1
def localDefeq (n : Nat) := n + 2

section
attribute [local crush_unfold] localUnfold
attribute [local crush_defeq] localDefeq
#eval checkUnfoldKind ``localUnfold (some .unfold)
#eval checkUnfoldKind ``localDefeq (some .defeq)
end
#eval checkUnfoldKind ``localUnfold none
#eval checkUnfoldKind ``localDefeq none

section
attribute [crush_unfold] localUnfold
attribute [crush_defeq] localDefeq
end
#eval checkUnfoldKind ``localUnfold (some .unfold)
#eval checkUnfoldKind ``localDefeq (some .defeq)

section
attribute [-crush_unfold] localUnfold
attribute [-crush_defeq] localDefeq
#eval checkUnfoldKind ``localUnfold none
#eval checkUnfoldKind ``localDefeq none
end
#eval checkUnfoldKind ``localUnfold (some .unfold)
#eval checkUnfoldKind ``localDefeq (some .defeq)

namespace ScopedUnfold
def increment (n : Nat) := n + 3
def incrementAgain (n : Nat) := n + 4
attribute [scoped crush_unfold] increment
attribute [scoped crush_defeq] incrementAgain
end ScopedUnfold
#eval checkUnfoldKind ``ScopedUnfold.increment none
#eval checkUnfoldKind ``ScopedUnfold.incrementAgain none
section
open scoped ScopedUnfold
#eval checkUnfoldKind ``ScopedUnfold.increment (some .unfold)
#eval checkUnfoldKind ``ScopedUnfold.incrementAgain (some .defeq)
end
#eval checkUnfoldKind ``ScopedUnfold.increment none
#eval checkUnfoldKind ``ScopedUnfold.incrementAgain none
