import Crush.Metatheory.SMT.Representation
import Crush.Metatheory.FO.Guarded

/-!
# Guard-aware SMT term encoding

Production represents some Lean carriers by a guarded subset of a larger SMT
sort. This wrapper keeps the ordinary sort and symbol encoding unchanged and
adds only the syntax used at quantifier boundaries.
-/

namespace Crush.Metatheory.SMT

open Defunctionalization.Flattened

private abbrev plainTerm {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) : STerm :=
  term encoding source

private abbrev plainArgs {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) {context : FO.Context}
    {sorts : List FO.FOSort} (args : FO.FamilyArgs symbols context sorts) :
    Array STerm :=
  arguments encoding args

/-- Guard syntax layered over the single ordinary FO-to-SMT encoding. `none`
means that every value of the represented sort is in the source image. -/
structure Guarding (symbols : FO.SymbolFamily) where
  encoding : Encoding symbols
  guard : FO.FOSort → STerm → Option STerm

mutual
  /-- Encode a typed term while guarding enlarged quantifier carriers exactly
  as production does. -/
  def Guarding.term {symbols : FO.SymbolFamily} (guarding : Guarding symbols) :
      {context : FO.Context} → {sort : FO.FOSort} →
        FO.FamilyTerm symbols context sort → STerm
    | _, _, .var ref => .bvar (varIndex ref)
    | _, _, .symbol symbol args =>
        .app (guarding.encoding.ident symbol) (guarding.arguments args)
    | _, _, .boolLit false => (smt| false)
    | _, _, .boolLit true => (smt| true)
    | _, _, .not body =>
        let body := guarding.term body
        (smt| (not $body))
    | _, _, .and left right =>
        let left := guarding.term left
        let right := guarding.term right
        (smt| (and $left $right))
    | _, _, .or left right =>
        let left := guarding.term left
        let right := guarding.term right
        (smt| (or $left $right))
    | _, _, .imp left right =>
        let left := guarding.term left
        let right := guarding.term right
        (smt| (=> $left $right))
    | _, _, .iff left right =>
        let left := guarding.term left
        let right := guarding.term right
        (smt| (= $left $right))
    | _, _, .eq left right =>
        let left := guarding.term left
        let right := guarding.term right
        (smt| (= $left $right))
    | _, _, .forallE (domain := domain) body =>
        let body := guarding.term body
        let value := Crush.SMT.Term.bvar 0
        let guarded := match guarding.guard domain value with
          | none => body
          | some condition => (smt| (=> $condition $body))
        .forallE #[("x", guarding.encoding.sort domain)] guarded
    | _, _, .existsE (domain := domain) body =>
        let body := guarding.term body
        let value := Crush.SMT.Term.bvar 0
        let guarded := match guarding.guard domain value with
          | none => body
          | some condition => (smt| (and $condition $body))
        .existsE #[("x", guarding.encoding.sort domain)] guarded

  /-- Encode a typed argument telescope in source order. -/
  def Guarding.arguments {symbols : FO.SymbolFamily}
      (guarding : Guarding symbols) :
      {context : FO.Context} → {sorts : List FO.FOSort} →
        FO.FamilyArgs symbols context sorts → Array STerm
    | _, _, .nil => #[]
    | _, _, .cons argument rest =>
        #[guarding.term argument] ++ guarding.arguments rest
end

attribute [simp] Guarding.term Guarding.arguments

/-- Exact guarded encoding relation for a typed term. -/
def GuardedTermRepresentation {symbols : FO.SymbolFamily}
    (guarding : Guarding symbols) {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) (target : STerm) : Prop :=
  target = guarding.term source

/-- Guard-aware assertions for a typed FO theory. -/
def Guarding.assertions {symbols : FO.SymbolFamily}
    (guarding : Guarding symbols) (source : FO.FamilyTheory symbols) :
    Array Command :=
  (source.map fun formula => .assert (guarding.term formula)).toArray

/-- Ordinary command suffix paired with guarded assertion syntax. Sort and
symbol declarations are shared with the unguarded encoder. -/
def Guarding.theoryBody {symbols : FO.SymbolFamily}
    (guarding : Guarding symbols) (declarations : List (Declaration symbols))
    (source : FO.FamilyTheory symbols) : Array Command :=
  ((ordinarySorts guarding.encoding declarations source).filterMap
      (sortDeclaration? guarding.encoding)).toArray ++
    ((ordinaryDecls guarding.encoding declarations).map
      (declaration guarding.encoding)).toArray ++
    guarding.assertions source

/-- Complete guarded command array. `derived` contains exact certified
definitions such as datatype `wf_T` predicates and is kept distinct from the
native datatype prefix. -/
def Guarding.theory {symbols : FO.SymbolFamily}
    (guarding : Guarding symbols) (derived : Array Command)
    (declarations : List (Declaration symbols))
    (source : FO.FamilyTheory symbols) : Array Command :=
  guarding.encoding.nativeCommands ++
    (derived ++ guarding.theoryBody declarations source)

/-- Exact syntax representation for a guarded theory and its certified derived
command segment. -/
def GuardedTheoryRepresentation {symbols : FO.SymbolFamily}
    (guarding : Guarding symbols) (derived : Array Command)
    (source : FO.FamilyTheory symbols) (commands : Array Command) : Prop :=
  ∃ declarations : List (Declaration symbols),
    commands = guarding.theory derived declarations source

/-- The ordinary encoder is the empty-guard specialization. -/
def Guarding.none {symbols : FO.SymbolFamily} (encoding : Encoding symbols) :
    Guarding symbols where
  encoding
  guard := fun _ _ => Option.none

@[simp] theorem Guarding.none_term {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) :
    (Guarding.none encoding).term source =
      plainTerm encoding source := by
  exact FO.FamilyTerm.rec
    (motive_1 := fun _ _ source =>
      (Guarding.none encoding).term source =
        plainTerm encoding source)
    (motive_2 := fun _ _ args =>
      (Guarding.none encoding).arguments args =
        plainArgs encoding args)
    (var := fun _ => rfl)
    (symbol := fun symbol args ih => by
      change Crush.SMT.Term.app (encoding.ident symbol)
        ((Guarding.none encoding).arguments args) =
          Crush.SMT.Term.app (encoding.ident symbol)
            (plainArgs encoding args)
      rw [ih])
    (boolLit := fun value => by cases value <;> rfl)
    (not := fun _ ih => by simp [ih])
    (and := fun _ _ leftIH rightIH => by simp [leftIH, rightIH])
    (or := fun _ _ leftIH rightIH => by simp [leftIH, rightIH])
    (imp := fun _ _ leftIH rightIH => by simp [leftIH, rightIH])
    (iff := fun _ _ leftIH rightIH => by simp [leftIH, rightIH])
    (eq := fun _ _ leftIH rightIH => by simp [leftIH, rightIH])
    (forallE := fun body ih => by
      change Crush.SMT.Term.forallE #[("x", encoding.sort _)]
          ((Guarding.none encoding).term body) =
        Crush.SMT.Term.forallE #[("x", encoding.sort _)]
          (plainTerm encoding body)
      rw [ih])
    (existsE := fun body ih => by
      change Crush.SMT.Term.existsE #[("x", encoding.sort _)]
          ((Guarding.none encoding).term body) =
        Crush.SMT.Term.existsE #[("x", encoding.sort _)]
          (plainTerm encoding body)
      rw [ih])
    (nil := rfl)
    (cons := fun _ _ headIH tailIH => by simp [headIH, tailIH])
    source

end Crush.Metatheory.SMT
