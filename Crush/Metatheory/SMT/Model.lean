import Crush.Metatheory.SMT.Representation

/-!
# Shared model induced by a typed FO model

This module contains the single raw SMT value universe and symbol graph used by
both ordinary declarations and native components. It is separated from the
top-level soundness composition so native datatype proofs can use the model
without creating an import cycle.
-/

namespace Crush.Metatheory.SMT

variable {symbols : FO.SymbolFamily}

/-- Values in the induced untyped SMT universe. -/
inductive Value (target : FO.FamilyModel symbols) where
  | typed (sort : FO.FOSort) (value : sort.Denote target.carriers)
  | raw (sort : SSort)

/-- A canonical inhabitant of every typed FO carrier. -/
noncomputable def defaultValue (carriers : FO.Carriers) :
    (sort : FO.FOSort) → sort.Denote carriers
  | .bool => True
  | .base sort => Classical.choice (carriers.baseNonempty sort)
  | .fn domain codomain => Classical.choice (carriers.fnNonempty domain codomain)

namespace Value

/-- Sort membership for the induced SMT universe. A raw value can inhabit only
a sort outside the image of the typed encoding. -/
def InSort (encoding : Encoding symbols) {target : FO.FamilyModel symbols}
    (smtSort : SSort) : Value target → Prop
  | .typed sort _ => encoding.sort sort = smtSort
  | .raw rawSort => rawSort = smtSort ∧
      ∀ sort, encoding.sort sort ≠ rawSort

@[simp] theorem inSort_typed (encoding : Encoding symbols)
    {target : FO.FamilyModel symbols} (sort : FO.FOSort)
    (value : sort.Denote target.carriers) :
    InSort encoding (encoding.sort sort) (.typed sort value) := rfl

/-- Membership in a represented sort exposes a uniquely typed FO value. -/
theorem exists_typed_of_inSort (encoding : Encoding symbols)
    {target : FO.FamilyModel symbols} (sort : FO.FOSort)
    (value : Value target) (typed : InSort encoding (encoding.sort sort) value) :
    ∃ sourceValue, value = .typed sort sourceValue := by
  cases value with
  | typed other value =>
      simp only [InSort] at typed
      have equal := encoding.sort_injective typed
      subst other
      exact ⟨value, rfl⟩
  | raw rawSort =>
      simp only [InSort] at typed
      exact False.elim (typed.2 sort typed.1.symm)

end Value

/-- Boolean embedding used by the induced SMT model. -/
def boolValue (target : FO.FamilyModel symbols) : Bool → Value target
  | false => .typed .bool False
  | true => .typed .bool True

/-- Decode an induced SMT value at an expected typed FO sort. Semantic term
evaluation reaches only the matching `typed` branch; defaults make symbol graphs
total over all raw inputs. -/
noncomputable def decode (target : FO.FamilyModel symbols)
    (sort : FO.FOSort) : Value target → sort.Denote target.carriers
  | .typed other value =>
      if equal : other = sort then equal ▸ value
      else defaultValue target.carriers sort
  | .raw _ => defaultValue target.carriers sort

@[simp] theorem decode_typed (target : FO.FamilyModel symbols)
    (sort : FO.FOSort) (value : sort.Denote target.carriers) :
    decode target sort (.typed sort value) = value := by
  simp [decode]

/-- Apply a curried typed symbol interpretation to an untyped value list. -/
noncomputable def applyValues (target : FO.FamilyModel symbols) :
    (sorts : List FO.FOSort) → {result : FO.FOSort} →
      FO.SymbolDenote target.carriers sorts result →
      List (Value target) → result.Denote target.carriers
  | [], _, function, _ => function
  | sort :: sorts, result, function, [] =>
      applyValues target sorts (result := result)
        (function (defaultValue target.carriers sort)) []
  | sort :: sorts, result, function, value :: values =>
      applyValues target sorts (result := result)
        (function (decode target sort value)) values

/-- Graph assigned to all encoded typed symbols, ordinary or native. -/
def Applies (encoding : Encoding symbols) (target : FO.FamilyModel symbols)
    (identifier : Crush.SMT.Ident) (values : List (Value target))
    (output : Value target) : Prop :=
  ∃ (decl : FO.SymbolDecl) (symbol : symbols decl),
    identifier = encoding.ident symbol ∧
    output = .typed decl.result
      (applyValues target decl.args (target.symbol symbol) values)

noncomputable def otherLiteralValue (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (literal : Crush.SMT.Literal) : Value target := by
  classical
  exact if represented : ∃ sort, encoding.sort sort = literal.sort then
    let sort := Classical.choose represented
    .typed sort (defaultValue target.carriers sort)
  else
    .raw literal.sort

noncomputable def literalValue (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) : Crush.SMT.Literal → Value target
  | .bool value => boolValue target value
  | literal@(.str _) => otherLiteralValue encoding target literal
  | literal@(.num _) => otherLiteralValue encoding target literal
  | literal@(.bitvec _ _) => otherLiteralValue encoding target literal

theorem literalValue_typed (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (literal : Crush.SMT.Literal) :
    Value.InSort encoding literal.sort (literalValue encoding target literal) := by
  cases literal with
  | bool value =>
      cases value <;> simpa [literalValue, Crush.SMT.Literal.sort, boolValue,
        Value.InSort] using encoding.bool_eq
  | str value | num value | bitvec width value =>
      classical
      rw [literalValue, otherLiteralValue]
      split
      next represented =>
        simp only [Value.InSort]
        exact Classical.choose_spec represented
      next notRepresented =>
        simp only [Value.InSort]
        constructor
        · trivial
        · intro sort equality
          exact notRepresented ⟨sort, equality⟩

/-- Additional derived-symbol graph carried by a native component. Disjointness
from every encoded source identifier guarantees that extending the model cannot
change the denotation or type of ordinary, constructor, selector, or tester
symbols. -/
structure ExtraGraph (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) where
  apply : Crush.SMT.Ident → List (Value target) → Value target → Prop
  source_fresh : ∀ {decl : FO.SymbolDecl} (symbol : symbols decl)
    (values : List (Value target)) (output : Value target),
    ¬apply (encoding.ident symbol) values output
  literal : Crush.SMT.Literal → Value target
  literal_typed : ∀ value : Crush.SMT.Literal,
    Value.InSort encoding value.sort (literal value)

/-- No derived symbols: the model used by the existing representation theorem. -/
noncomputable def ExtraGraph.nil (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) : ExtraGraph encoding target where
  apply := fun _ _ _ => False
  source_fresh := by simp
  literal := literalValue encoding target
  literal_typed := literalValue_typed encoding target

/-- Union of the ordinary encoded graph and a disjoint native extension. -/
def AppliesWith (encoding : Encoding symbols) (target : FO.FamilyModel symbols)
    (extra : ExtraGraph encoding target) (identifier : Crush.SMT.Ident)
    (values : List (Value target)) (output : Value target) : Prop :=
  Applies encoding target identifier values output ∨
    extra.apply identifier values output

/-- Common induced-model construction parameterized only by its symbol graph. -/
@[reducible] private noncomputable def modelOfGraph (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols)
    (graph : Crush.SMT.Ident → List (Value target) → Value target → Prop)
    (literal : Crush.SMT.Literal → Value target)
    (literalTyped : ∀ value,
      Value.InSort encoding value.sort (literal value)) :
    Crush.SMT.Model where
  Value := Value target
  inSort := Value.InSort encoding
  sortNonempty := fun smtSort => by
    classical
    by_cases represented : ∃ sort, encoding.sort sort = smtSort
    · let sort := Classical.choose represented
      have equality := Classical.choose_spec represented
      exact ⟨Value.typed sort (defaultValue target.carriers sort), equality⟩
    · exact ⟨Value.raw smtSort, rfl, by
        intro sort equality
        exact represented ⟨sort, equality⟩⟩
  bool := boolValue target
  boolTyped := fun value => by
    cases value <;> simpa [boolValue, Value.InSort] using encoding.bool_eq
  boolInjective := by
    intro left right equality
    cases left <;> cases right
    · rfl
    · have impossible : False = True := eq_of_heq (Value.typed.inj equality).2
      exact False.elim (Eq.mpr impossible trivial)
    · have impossible : True = False := eq_of_heq (Value.typed.inj equality).2
      exact False.elim (Eq.mp impossible trivial)
    · rfl
  literal
  literalTyped
  apply := graph

/-- Concrete SMT model induced by a typed FO family model and a disjoint
graph for native derived symbols. -/
noncomputable def modelWith (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target) :
    Crush.SMT.Model :=
  modelOfGraph encoding target (AppliesWith encoding target extra)
    extra.literal extra.literal_typed

/-- The ordinary induced model is the empty native-graph specialization. -/
noncomputable def model (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) : Crush.SMT.Model :=
  modelOfGraph encoding target (Applies encoding target)
    (literalValue encoding target) (literalValue_typed encoding target)

@[simp] theorem model_inSort (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (sort : SSort) (value : Value target) :
    (model encoding target).inSort sort value ↔
      Value.InSort encoding sort value := Iff.rfl

@[simp] theorem modelWith_inSort (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (sort : SSort) (value : Value target) :
    (modelWith encoding target extra).inSort sort value ↔
      Value.InSort encoding sort value := Iff.rfl

@[simp] theorem model_bool (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (value : Bool) :
    (model encoding target).bool value = boolValue target value := rfl

@[simp] theorem modelWith_bool (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (value : Bool) :
    (modelWith encoding target extra).bool value = boolValue target value := rfl

/-- The Boolean carrier of every induced model contains exactly the two
distinguished SMT Boolean values. Although the typed carrier is represented by
Lean propositions, classical propositional extensionality identifies each
proposition with either `True` or `False`. -/
theorem modelWith_bool_exhaustive (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target) :
    ∀ value, (modelWith encoding target extra).inSort Crush.SMT.boolSort value →
      ∃ boolean, value = (modelWith encoding target extra).bool boolean := by
  classical
  intro value typed
  cases value with
  | typed sort proposition =>
      simp only [modelWith_inSort, Value.InSort] at typed
      have sortEq : sort = .bool := by
        apply encoding.sort_injective
        exact typed.trans encoding.bool_eq.symm
      subst sort
      by_cases valid : proposition
      · refine ⟨true, ?_⟩
        have equal : proposition = True :=
          propext ⟨fun _ => trivial, fun _ => valid⟩
        cases equal
        rfl
      · refine ⟨false, ?_⟩
        have equal : proposition = False := propext ⟨valid, False.elim⟩
        cases equal
        rfl
  | raw rawSort =>
      simp only [modelWith_inSort, Value.InSort] at typed
      exact False.elim (typed.2 .bool (encoding.bool_eq.trans typed.1.symm))

/-- With no derived-symbol graph, the induced source-symbol graph is globally
single-valued. This is the base case reused by translations that need neither
integer operations nor datatype guard predicates. -/
theorem modelWith_nil_applyUnique (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) :
    Crush.SMT.ApplyUnique
      (modelWith encoding target (ExtraGraph.nil encoding target)) := by
  intro identifier values left right leftApply rightApply
  rcases leftApply with leftOrdinary | leftExtra
  · rcases rightApply with rightOrdinary | rightExtra
    · rcases leftOrdinary with
        ⟨leftDecl, leftSymbol, leftIdent, leftOutput⟩
      rcases rightOrdinary with
        ⟨rightDecl, rightSymbol, rightIdent, rightOutput⟩
      have identEq : encoding.ident leftSymbol = encoding.ident rightSymbol :=
        leftIdent.symm.trans rightIdent
      have declEq := encoding.ident_decl_injective leftSymbol rightSymbol identEq
      subst rightDecl
      have symbolEq := encoding.ident_injective leftSymbol rightSymbol identEq
      subst rightSymbol
      exact leftOutput.trans rightOutput.symm
    · simp [ExtraGraph.nil] at rightExtra
  · simp [ExtraGraph.nil] at leftExtra

/-- Every source symbol keeps its encoded type after adding a disjoint native
graph. -/
theorem symbol_has_type_with (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    {decl : FO.SymbolDecl} (symbol : symbols decl) :
    Crush.SMT.SymbolHasType (modelWith encoding target extra)
      (encoding.ident symbol) (decl.args.map encoding.sort)
      (encoding.sort decl.result) := by
  intro values valuesTyped
  let output := Value.typed decl.result
    (applyValues target decl.args (target.symbol symbol) values)
  refine ⟨output, ?_, ?_, ?_⟩
  · dsimp only [output]
    exact Value.inSort_typed (target := target) encoding decl.result
      (applyValues target decl.args (target.symbol symbol) values)
  · exact Or.inl ⟨decl, symbol, rfl, rfl⟩
  · intro other otherApplies
    rcases otherApplies with ordinary | native
    · rcases ordinary with ⟨otherDecl, otherSymbol, identEqual, outputEqual⟩
      have declEqual := encoding.ident_decl_injective symbol otherSymbol identEqual
      subst otherDecl
      have symbolEqual := encoding.ident_injective symbol otherSymbol identEqual
      subst otherSymbol
      exact outputEqual
    · exact False.elim (extra.source_fresh symbol values other native)

/-- A native extension is observationally invisible at every encoded source
identifier. This is the preservation fact reused by ordinary terms and native
datatype constructors, selectors, and testers. -/
theorem applies_source_iff (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    {decl : FO.SymbolDecl} (symbol : symbols decl)
    (values : List (Value target)) (output : Value target) :
    (modelWith encoding target extra).apply
        (encoding.ident symbol) values output ↔
      (model encoding target).apply
        (encoding.ident symbol) values output := by
  constructor
  · intro applied
    rcases applied with ordinary | native
    · exact ordinary
    · exact False.elim (extra.source_fresh symbol values output native)
  · intro applied
    exact Or.inl applied

/-- Every typed FO symbol has its encoded type in the single induced model,
independently of which component declares it. -/
theorem symbol_has_type (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {decl : FO.SymbolDecl}
    (symbol : symbols decl) :
    Crush.SMT.SymbolHasType (model encoding target) (encoding.ident symbol)
      (decl.args.map encoding.sort) (encoding.sort decl.result) := by
  intro values valuesTyped
  let output := Value.typed decl.result
    (applyValues target decl.args (target.symbol symbol) values)
  refine ⟨output, ?_, ?_, ?_⟩
  · dsimp only [output]
    exact Value.inSort_typed (target := target) encoding decl.result
      (applyValues target decl.args (target.symbol symbol) values)
  · exact ⟨decl, symbol, rfl, rfl⟩
  · intro other otherApplies
    rcases otherApplies with ⟨otherDecl, otherSymbol, identEqual, outputEqual⟩
    have declEqual := encoding.ident_decl_injective symbol otherSymbol identEqual
    subst otherDecl
    have symbolEqual := encoding.ident_injective symbol otherSymbol identEqual
    subst otherSymbol
    exact outputEqual

end Crush.Metatheory.SMT
