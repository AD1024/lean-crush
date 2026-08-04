import Crush

/-!
Retargeting a user type to SMT's **Array theory** via the metaprogramming API.

This demonstrates the extension layer end-to-end: a `@[crush_translate_sort]` handler
maps a Lean type to the theory sort `(Array K V)`, and `@[crush_translate]` handlers
map its operations to `select`/`store`/`const`. No change to the core translator is
needed — the whole encoding is user code.

`AMap κ ν` is a *total* map (every key has a value), which is exactly SMT's array
model: `(Array K V)` is a total function `K → V`. `get`/`set` are `select`/`store`.
-/

open Crush Crush.SMT

/-- A total map — SMT's array model exactly: a total function from keys to values.
The Lean model is honest (a wrapped `κ → ν`), but translation replaces the type and
its operations wholesale with the Array theory, so only the operation *signatures*
drive the encoding. -/
structure AMap (κ : Type) (ν : Type) where
  fn : κ → ν

namespace AMap
def get {κ ν : Type} (m : AMap κ ν) (k : κ) : ν := m.fn k
def set {κ ν : Type} [DecidableEq κ] (m : AMap κ ν) (k : κ) (v : ν) : AMap κ ν :=
  ⟨fun k' => if k' = k then v else m.fn k'⟩
end AMap
-- Note: SMT's constant array `((as const (Array K V)) v)` is *not* demonstrated here.
-- It needs a sort-annotated (`as`) qualified identifier, which the current `SMT.Ident`
-- IR (`symb`/`indexed`) cannot express — a real IR gap, not a handler-API limitation.
-- `select`/`store` need no annotation and are fully reachable from user handlers.

/-! ## The encoding, as user metaprograms

The sort handler turns `AMap K V` into `(Array ⟦K⟧ ⟦V⟧)`. The operation handlers turn
`get`/`set` into `select`/`store`. -/

@[crush_translate_sort]
def amapSort : SortHandler := fun ctx => do
  let .const ``AMap _ := ctx.fn | return none
  match ctx.args with
  | #[k, v] => return some (.app (.symb "Array") #[← ctx.emitSort k, ← ctx.emitSort v])
  | _ => return none

@[crush_translate]
def amapGet : TranslationHandler := fun ctx => do
  let .const ``AMap.get _ := ctx.fn | return none
  -- `@AMap.get κ ν m k` — the two leading type args are dropped by the encoding.
  match ctx.args with
  | #[_, _, m, k] => return some (.symbApp "select" #[← ctx.emitTerm m, ← ctx.emitTerm k])
  | _ => return none

@[crush_translate]
def amapSet : TranslationHandler := fun ctx => do
  let .const ``AMap.set _ := ctx.fn | return none
  -- `@AMap.set κ ν inst m k v` — drop the two type args and the `DecidableEq` instance.
  match ctx.args with
  | #[_, _, _, m, k, v] =>
    return some (.symbApp "store" #[← ctx.emitTerm m, ← ctx.emitTerm k, ← ctx.emitTerm v])
  | _ => return none

set_option crush.trust "trust"

/-! ## The SMT Array axioms now hold for `AMap`, for free

These are the read-over-write axioms of the theory of arrays. `crush` proves them
because the encoding put the operations into that theory — none of this is asserted
in Lean. -/

-- Read-over-write, same key: `get (set m k v) k = v`.
theorem amap_row_same (m : AMap Int Int) (k v : Int) :
    AMap.get (AMap.set m k v) k = v := by crush

-- Read-over-write, different key: `k₁ ≠ k₂ → get (set m k₁ v) k₂ = get m k₂`.
theorem amap_row_diff (m : AMap Int Int) (k₁ k₂ v : Int) (h : k₁ ≠ k₂) :
    AMap.get (AMap.set m k₁ v) k₂ = AMap.get m k₂ := by crush

-- Extensionality-flavored: two stores at the same key/value agree.
theorem amap_store_congr (m : AMap Int Int) (k v w : Int) (h : v = w) :
    AMap.set m k v = AMap.set m k w := by crush

-- A mixed key/value instantiation `AMap Int Bool` uses `(Array Int Bool)`.
theorem amap_bool_row (m : AMap Int Bool) (k : Int) (b : Bool) :
    AMap.get (AMap.set m k b) k = b := by crush

-- Negative test: a *false* array fact must be refuted, not closed. `get (set m k v) k`
-- is `v`, not necessarily anything else, so `= w` for an unrelated `w` is false.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem amap_row_false (m : AMap Int Int) (k v w : Int) :
    AMap.get (AMap.set m k v) k = w := by crush
