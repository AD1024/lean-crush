import Crush

/-!
Tests for the hint grammar:

```
crush [h₁, …, *] u[f₁, …] d[g₁, …]
```

These exercise the capability that the argumentless tactic lacked entirely:
pointing `crush` at a lemma that is *not* a local hypothesis, restricting to an
explicit fact list, and pulling in a definition's equation lemmas.
-/

open Crush

set_option crush.trust "trust"

/-! ## Explicit lemma hints — the headline new capability

`extra_fact` is a top-level lemma, not a hypothesis of the goal. Bare `crush` cannot
see it; `crush [extra_fact]` asserts it and the goal closes. -/

axiom P : Int → Prop
axiom extra_fact : ∀ x : Int, P x

theorem uses_named_lemma (a : Int) : P a := by
  crush [extra_fact]

-- Combining an explicit lemma with the local context via `*`.
theorem lemma_plus_star (a b : Int) (h : a = b) : P a ∧ b = a := by
  crush [extra_fact, *]

/-! ## An explicit list *without* `*` restricts to the listed facts

`crush [h1]` asserts only `h1` (and the goal), *not* `h2`. Here the goal follows
from `h1` alone, so it closes; the point is that the list is a restriction, not an
addition to the full context. -/

theorem explicit_list_restricts (a b c : Int) (h1 : a = b) (h2 : b = c) : a = b := by
  crush [h1]

/-! ## Bare `crush` still sweeps the whole context (regression) -/

theorem bare_still_uses_all (a b c : Int) (h1 : a = b) (h2 : b = c) : a = c := by
  crush

/-! ## `u[…]` unfolds a definition via its equation lemmas

`crush` treats `double` as an uninterpreted symbol without help, so it cannot see
`double 3 = 6`. `u[double]` adds `double`'s defining equation, after which the goal
is linear arithmetic. -/

def double (n : Int) : Int := n + n

theorem unfold_definition : double 3 = 6 := by
  crush u[double]

-- `u[…]` also lets a fact *about* the unfolded symbol go through.
theorem unfold_with_hyp (x : Int) (h : x = 5) : double x = 10 := by
  crush [h] u[double]

/-! ## `d[…]` uses the single unfold equation

For a plain (non-recursive) definition, `d[f]` and `u[f]` coincide; the grammar is
accepted and the definition unfolds. -/

def triple (n : Int) : Int := n + n + n

theorem defeq_unfold : triple 2 = 6 := by
  crush d[triple]

/-! ## Diagnostics for malformed hints

A non-`Prop` term hint is rejected with a message naming the offending hint, rather
than silently producing a bad script. -/

/-- error: crush: hint (37 : Int) has type `Int`, which is not a `Prop` -/
#guard_msgs(error, substring := true) in
theorem rejects_non_prop_hint (a : Int) : a = a := by
  crush [(37 : Int)]

-- Unfolding something with no equational lemmas (an `axiom`) is a clear error.
/-- error: crush: `P` has no unfold equation. -/
#guard_msgs(error, substring := true) in
theorem rejects_unfoldable (a : Int) : a = a := by
  crush d[P]
