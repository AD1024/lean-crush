import Crush

/-!
# Datatypes with untranslatable fields become opaque

A structure whose field sort cannot be translated (a dependent type such as `Fin 5`
or a quotient by a relation) is declared under rollback: the declaration is undone
and the type becomes an opaque sort everywhere in the query, guarded unless it is
known to be inhabited (review round 3, C5). A structure whose field type mentions an
earlier field has no single SMT selector sort and is opaque by a static rule (N2).
The fallback is local: a structure with such a field type stays a datatype.
-/

set_option crush.timeout 10

namespace OpaqueDatatypes

structure Wrap where
  val : Fin 5

example (a b c : Wrap) (h : a = b) (h2 : b = c) : a = c := by crush
example (f : Wrap → Int) (a b : Wrap) (h : a = b) (h2 : f a = 3) : f b = 3 := by crush

-- An opaque sort must not gain datatype semantics.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example (a b : Wrap) (h : a.val = b.val) : a = b := by crush

structure Sig where
  α : Type
  x : α

example (s t : Sig) (h : s = t) : t = s := by crush
example (s : Sig) (f : Sig → Int) (h : f s > 0) : f s ≥ 0 := by crush

def sameParity (a b : Int) : Prop := a % 2 = b % 2

structure QBox where
  q : Quot sameParity

example (a b c : QBox) (h : a = b) (h2 : b = c) : a = c := by crush

example (a b c : Option (Fin 5)) (h : a = b) (h2 : b = c) : a = c := by crush
example (a b c : Array (Fin 5)) (h : a = b) (h2 : b = c) : a = c := by crush
example (a b : Array (Fin 5)) (f : Array (Fin 5) → Int) (h : a = b) : f a = f b := by crush

-- The fallback stays local: `Outer` is a datatype over the opaque `Wrap` sort.
structure Outer where
  w : Wrap
  n : Int

theorem outer_is_datatype (a b : Outer) (h : a.w = b.w) (h2 : a.n = b.n) : a = b := by
  crush

-- A field of `Decidable p` uses the built-in `Decidable` sort handler, so `DecBox`
-- stays a datatype, and its one constructor over a subsingleton proves `a = b`.
structure DecBox (p : Prop) where
  dec : Decidable p

theorem decbox_is_datatype (p : Prop) (a b : DecBox p) : a = b := by crush

-- One query: `Wrap` is opaque both where it occurs directly and inside `Outer`.
example (o : Outer) (w : Wrap) (h : o.w = w) (f : Wrap → Int) (h2 : f w = 1) :
    f o.w = 1 := by crush

end OpaqueDatatypes
