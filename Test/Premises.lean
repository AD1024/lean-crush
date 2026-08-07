import Crush

/-!
Tests for bounded premise selection through Lean core's `LibrarySuggestions`.

The custom selector makes the test deterministic. Production code uses whatever
selector is registered by the importing project; importing `Crush` installs Lean's
default SineQuaNon/current-file engine.
-/

open Lean
open Lean.LibrarySuggestions
open Crush

namespace PremiseSelection

axiom SelectedP {α : Type} : α → Prop
axiom selectedLemma : ∀ {α : Type} (x : α), SelectedP x

@[library_suggestions]
meta def selectedOnly : Selector := fun _ cfg =>
  return (#[{ name := ``selectedLemma, score := 1.0 }]).take cfg.maxSuggestions

set_option crush.trust "reconstruct"

set_option crush.premises true in
set_option crush.premises.max 1 in
theorem uses_selected_library_lemma (x : Int) : SelectedP x := by
  crush

-- Selected polymorphic theorems pass through ordinary monomorphization. A zero
-- bound disables selection even when the feature itself is enabled.
set_option crush.premises true in
set_option crush.premises.max 0 in
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem zero_bound_selects_nothing (x : Int) : SelectedP x := by
  crush

-- Selection is opt-in, so existing bare `crush` behavior does not silently grow
-- every query.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem selection_disabled_by_default (x : Int) : SelectedP x := by
  crush

-- An explicit list remains a strict restriction even when the global option is on.
set_option crush.premises true in
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem explicit_list_disables_selection (x : Int) : SelectedP x := by
  crush []

end PremiseSelection
