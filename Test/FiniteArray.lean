import Crush

/-!
Core regressions for the finite Lean `Array` encoding.

Lean arrays are represented by a logical length and an SMT theory array.
These tests cover the semantic bridge between bounded/defaulting reads, guarded
writes, recursive well-formedness, and extensional equality.
-/

open Crush

set_option crush.timeout 5

theorem finiteArray_getElem_bang_pos
    (arr : Array Int) (i : Nat) (h : i < arr.size) :
    arr[i]! = arr[i]'h := by
  crush

theorem finiteArray_set_same
    (arr : Array Int) (i : Nat) (value : Int) (h : i < arr.size) :
    (arr.set! i value)[i]! = value := by
  crush

theorem finiteArray_set_different
    (arr : Array Int) (i j : Nat) (value : Int)
    (hj : j < arr.size) (hne : j ≠ i) :
    (arr.set! i value)[j]! = arr[j]! := by
  crush

theorem finiteArray_set_out_of_bounds
    (arr : Array Int) (i : Nat) (value : Int) (h : arr.size ≤ i) :
    arr.set! i value = arr := by
  crush

theorem finiteArray_set_size
    (arr : Array Int) (i : Nat) (value : Int) :
    (arr.set! i value).size = arr.size := by
  crush

theorem finiteArray_bounded_set
    (arr : Array Int) (i : Nat) (value : Int) (h : i < arr.size) :
    (arr.set i value h)[i]! = value := by
  crush

theorem finiteArray_setIfInBounds_out
    (arr : Array Int) (i : Nat) (value : Int) (h : arr.size ≤ i) :
    arr.setIfInBounds i value = arr := by
  crush

theorem finiteArray_push_size (arr : Array Int) (value : Int) :
    (arr.push value).size = arr.size + 1 := by
  crush

theorem finiteArray_push_new (arr : Array Int) (value : Int) :
    (arr.push value)[arr.size]! = value := by
  crush

theorem finiteArray_push_old
    (arr : Array Int) (i : Nat) (value : Int) (h : i < arr.size) :
    (arr.push value)[i]! = arr[i]! := by
  crush

theorem finiteArray_replicate_size (n : Nat) (value : Int) :
    (Array.replicate n value).size = n := by
  crush

theorem finiteArray_replicate_read :
    (Array.replicate 1 (7 : Int))[0]! = 7 := by
  crush

theorem finiteArray_replicate_out_of_bounds :
    (Array.replicate 1 (7 : Int))[1]? = none := by
  crush

theorem finiteArray_replicate_symbolic
    (n i : Nat) (value : Int) (h : i < n) :
    (Array.replicate n value)[i]! = value := by
  crush

theorem finiteArray_pop_size (arr : Array Int) :
    arr.pop.size = arr.size - 1 := by
  crush

theorem finiteArray_pop_read
    (arr : Array Int) (i : Nat) (h : i < arr.pop.size) :
    arr.pop[i]! = arr[i]! := by
  crush

theorem finiteArray_pop_push (arr : Array Int) (value : Int) :
    (arr.push value).pop = arr := by
  crush

theorem finiteArray_swap_left
    (arr : Array Int) (i j : Nat)
    (hi : i < arr.size) (hj : j < arr.size) :
    (arr.swap i j hi hj)[i]! = arr[j]! := by
  crush

theorem finiteArray_swap_right
    (arr : Array Int) (i j : Nat)
    (hi : i < arr.size) (hj : j < arr.size) :
    (arr.swap i j hi hj)[j]! = arr[i]! := by
  crush

theorem finiteArray_swapIfInBounds_out
    (arr : Array Int) (i j : Nat) (hi : arr.size ≤ i) :
    arr.swapIfInBounds i j = arr := by
  crush

theorem finiteArray_getElem?_pos
    (arr : Array Int) (i : Nat) (h : i < arr.size) :
    arr[i]? = some (arr[i]'h) := by
  crush

theorem finiteArray_getElem?_out
    (arr : Array Int) (i : Nat) (h : arr.size ≤ i) :
    arr[i]? = none := by
  crush

theorem finiteArray_isEmpty_pos
    (arr : Array Int) (h : arr.size = 0) :
    arr.isEmpty = true := by
  crush

theorem finiteArray_isEmpty_neg
    (arr : Array Int) (h : arr.size ≠ 0) :
    arr.isEmpty = false := by
  crush

theorem finiteArray_back!_push (arr : Array Int) (value : Int) :
    (arr.push value).back! = value := by
  crush

theorem finiteArray_back?_push (arr : Array Int) (value : Int) :
    (arr.push value).back? = some value := by
  crush

/-! Downstream Array operations can use the same representation API. -/

def overwriteFirst {α : Type} (arr : Array α) (value : α) : Array α :=
  arr.setIfInBounds 0 value

@[crush_translate_head overwriteFirst]
def overwriteFirstLowering : LoweringHandler := fun ctx => do
  let #[elem, arr, value] := ctx.args | return none
  let svalue ← ctx.emitTerm value
  withFiniteArray ctx elem arr fun view => do
    let stored := (smt| (store $(view.data) 0 $svalue))
    let updated := view.mkValue view.length stored
    return (smt| (ite (> $(view.length) 0) $updated $(view.value)))

theorem finiteArray_custom_lowering
    (arr : Array Int) (value : Int) (h : 0 < arr.size) :
    (overwriteFirst arr value)[0]! = value := by
  crush

theorem finiteArray_nat_element_wf :
    ∀ (arr : Array Nat) (i : Nat) (h : i < arr.size),
      (0 : Int) ≤ (arr[i]'h : Int) := by
  crush

theorem finiteArray_nested_size_wf :
    ∀ (arr : Array (Array Int)) (i : Nat) (h : i < arr.size),
      (0 : Nat) ≤ (arr[i]'h).size := by
  crush

theorem finiteArray_empty_size (arr : Array Empty) :
    arr.size = 0 := by
  crush

theorem finiteArray_extensional
    (left right : Array Int)
    (hsize : left.size = right.size)
    (hget : ∀ i, i < left.size → left[i]! = right[i]!) :
    left = right := by
  crush

/-- error: crush: -/
#guard_msgs(error, substring := true) in
theorem finiteArray_false_read
    (arr : Array Int) (i : Nat) (value other : Int)
    (h : i < arr.size) :
    (arr.set! i value)[i]! = other := by
  crush

/-!
A sort handler may intentionally replace Lean Array's representation. Built-in
Array operation lowering must then defer as well, rather than applying finite
Array selectors to a value of the custom sort.
-/

open Crush.SMT

@[crush_translate_sort high]
def finiteArrayTestSortOverride : SortHandler := fun ctx => do
  let .const ``Array _ := ctx.fn | return none
  let #[elem] := ctx.args | return none
  unless (← Lean.Meta.whnf elem).isConstOf ``Int do return none
  return some (.app (.symb "Int") #[])

theorem finiteArray_sort_override_congruence
    (left right : Array Int) (h : left = right) :
    left.size = right.size := by
  crush
