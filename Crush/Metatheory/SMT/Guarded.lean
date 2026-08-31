import Crush.Metatheory.SMT.Representation
import Crush.Metatheory.FO.Guarded

/-!
# Guard-aware SMT term encoding

The Crush translator represents some Lean carriers by a guarded subset of a larger SMT
sort. This wrapper keeps the ordinary sort and symbol encoding unchanged and
adds only the syntax used at quantifier boundaries.
-/

namespace Crush.Metatheory.SMT

open Defunctionalization.Flattened

/-- Guard syntax layered over the single ordinary FO-to-SMT encoding. `none`
means that every value of the represented sort is in the source image. -/
structure GuardedEncoding (symbols : FO.SymbolFamily) where
  encoding : Encoding symbols
  guard : FO.FOSort → STerm → Option STerm

/-- Encode a typed term with this guarding policy at quantifier boundaries. -/
def GuardedEncoding.term {symbols : FO.SymbolFamily} (guarding : GuardedEncoding symbols) :
    {context : FO.Context} → {sort : FO.FOSort} →
      FO.FamilyTerm symbols context sort → STerm :=
  encodeTerm guarding.encoding guarding.guard

/-- Encode a typed argument telescope using the same guarding policy. -/
def GuardedEncoding.arguments {symbols : FO.SymbolFamily}
    (guarding : GuardedEncoding symbols) :
    {context : FO.Context} → {sorts : List FO.FOSort} →
      FO.FamilyArgs symbols context sorts → Array STerm :=
  encodeArguments guarding.encoding guarding.guard

attribute [simp] GuardedEncoding.term GuardedEncoding.arguments

set_option quotPrecheck false

/-- `𝒢⟦e⟧[G]` is the concrete SMT term produced with guarding policy `G`. -/
scoped notation:max "𝒢⟦" source "⟧[" guarding "]" =>
  GuardedEncoding.term guarding source

/-- Guard-aware assertions for a typed FO theory. -/
def GuardedEncoding.assertions {symbols : FO.SymbolFamily}
    (guarding : GuardedEncoding symbols) (source : FO.FamilyTheory symbols) :
    Array Command :=
  (source.map fun φ => .assert 𝒢⟦φ⟧[guarding]).toArray

/-- Ordinary command suffix paired with guarded assertion syntax. Sort and
symbol declarations are shared with the unguarded encoder. -/
def GuardedEncoding.theoryBody {symbols : FO.SymbolFamily}
    (guarding : GuardedEncoding symbols) (declarations : List (Declaration symbols))
    (source : FO.FamilyTheory symbols) : Array Command :=
  ((ordinarySorts guarding.encoding declarations source).filterMap
      (sortDeclaration? guarding.encoding)).toArray ++
    ((ordinaryDecls guarding.encoding declarations).map
      (declaration guarding.encoding)).toArray ++
    guarding.assertions source

/-- Complete guarded command array. `derived` contains checked definitions such
as datatype `wf_T` predicates and is kept distinct from the
native datatype prefix. -/
def GuardedEncoding.theory {symbols : FO.SymbolFamily}
    (guarding : GuardedEncoding symbols) (derived : Array Command)
    (declarations : List (Declaration symbols))
    (source : FO.FamilyTheory symbols) : Array Command :=
  guarding.encoding.nativeCommands ++
    (derived ++ guarding.theoryBody declarations source)

/-- Semantic command-set representation for a guarded theory and its separately
checked derived-command segment. The Crush translator may interleave declarations and assertions
or omit duplicate occurrences without changing this model-theoretic boundary. -/
def GuardedTheoryRepresentation {symbols : FO.SymbolFamily}
    (guarding : GuardedEncoding symbols) (derived : Array Command)
    (source : FO.FamilyTheory symbols) (commands : Array Command) : Prop :=
  ∃ declarations : List (Declaration symbols),
    Crush.SMT.SameCommandSet commands
      (guarding.theory derived declarations source)

/-- The ordinary encoder is the empty-guard specialization. -/
def GuardedEncoding.none {symbols : FO.SymbolFamily} (encoding : Encoding symbols) :
    GuardedEncoding symbols where
  encoding
  guard := fun _ _ => Option.none

@[simp] theorem GuardedEncoding.none_term {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) :
    (GuardedEncoding.none encoding).term source =
      SMT.term encoding source := rfl

end Crush.Metatheory.SMT
