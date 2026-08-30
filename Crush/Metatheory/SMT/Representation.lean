import Crush.Metatheory.Defunctionalization.Flattened.Theory
import Crush.Metatheory.SMT.Semantics
import Crush.SMT.Quote

/-!
# Representation of intrinsic first-order syntax as concrete SMT syntax

This module defines a pure specification encoder.  Its representation
predicates are deliberately syntactic: they say exactly which concrete sort,
identifier, term, or command sequence was produced.  Semantic preservation is
proved in `SMT.Soundness` and remains distinct from these syntax facts.
-/

namespace Crush.Metatheory.SMT

abbrev SSort := Crush.SMT.SSort
abbrev STerm := Crush.SMT.Term
abbrev Command := Crush.SMT.Command

open Defunctionalization.Flattened

/-- One concrete representation of an abstract typed FO symbol family.

Most symbols are emitted as ordinary `declare-fun` commands. Native SMT
declarations (currently monomorphic datatype blocks) instead contribute a
command prefix and mark the sorts and symbols that prefix declares. Keeping
this policy here gives ordinary and datatype symbols one term encoder, one
identifier namespace, and one semantic model. -/
structure Encoding (symbols : FO.SymbolFamily) where
  sort : FO.FOSort → SSort
  sort_injective : Function.Injective sort
  bool_eq : sort .bool = Crush.SMT.boolSort
  name : {decl : FO.SymbolDecl} → symbols decl → String
  ident : {decl : FO.SymbolDecl} → symbols decl → Crush.SMT.Ident
  ident_decl_injective : ∀ {leftDecl rightDecl : FO.SymbolDecl}
    (left : symbols leftDecl) (right : symbols rightDecl),
    ident left = ident right → leftDecl = rightDecl
  ident_injective : ∀ {decl : FO.SymbolDecl} (left right : symbols decl),
    ident left = ident right → left = right
  ident_fresh : ∀ {decl : FO.SymbolDecl} (symbol : symbols decl),
    Crush.SMT.NotBuiltin (ident symbol)
  nativeSort : FO.FOSort → Bool
  nativeSymbol : {decl : FO.SymbolDecl} → symbols decl → Bool
  nativeCommands : Array Command
  ordinary_ident : ∀ {decl : FO.SymbolDecl} (symbol : symbols decl),
    nativeSymbol symbol = false → ident symbol = .symb (name symbol)

/-- A concrete SMT sort is exactly the selected representation of an intrinsic
FO sort. -/
def SortRepresentation {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) (sort : FO.FOSort) (smt : SSort) : Prop :=
  smt = encoding.sort sort

/-- A concrete SMT identifier is exactly the selected name of a typed symbol. -/
def SymbolRepresentation {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) {decl : FO.SymbolDecl}
    (symbol : symbols decl) (identifier : Crush.SMT.Ident) : Prop :=
  identifier = encoding.ident symbol

/-- Numeric de Bruijn index of an intrinsic FO variable. -/
def varIndex : {context : FO.Context} → {sort : FO.FOSort} →
    FO.Var context sort → Nat
  | _ :: _, _, .here => 0
  | _ :: _, _, .there ref => varIndex ref + 1

mutual
  /-- Pure encoding of an intrinsically typed family term. -/
  def term {symbols : FO.SymbolFamily} (encoding : Encoding symbols) :
      {context : FO.Context} → {sort : FO.FOSort} →
        FO.FamilyTerm symbols context sort → STerm
    | _, _, .var ref => .bvar (varIndex ref)
    | _, _, .symbol symbol args =>
        .app (encoding.ident symbol)
          (arguments encoding args)
    | _, _, .boolLit false => (smt| false)
    | _, _, .boolLit true => (smt| true)
    | _, _, .not body =>
        let body := term encoding body
        (smt| (not $body))
    | _, _, .and left right =>
        let left := term encoding left
        let right := term encoding right
        (smt| (and $left $right))
    | _, _, .or left right =>
        let left := term encoding left
        let right := term encoding right
        (smt| (or $left $right))
    | _, _, .imp left right =>
        let left := term encoding left
        let right := term encoding right
        (smt| (=> $left $right))
    | _, _, .iff left right =>
        let left := term encoding left
        let right := term encoding right
        (smt| (= $left $right))
    | _, _, .eq left right =>
        let left := term encoding left
        let right := term encoding right
        (smt| (= $left $right))
    | _, _, .forallE (domain := domain) body =>
        .forallE #[("x", encoding.sort domain)] (term encoding body)
    | _, _, .existsE (domain := domain) body =>
        .existsE #[("x", encoding.sort domain)] (term encoding body)

  /-- Pure encoding of a typed argument telescope in source order. -/
  def arguments {symbols : FO.SymbolFamily} (encoding : Encoding symbols) :
      {context : FO.Context} → {sorts : List FO.FOSort} →
        FO.FamilyArgs symbols context sorts → Array STerm
    | _, _, .nil => #[]
    | _, _, .cons argument rest =>
        #[term encoding argument] ++ arguments encoding rest
end

attribute [simp] term arguments

/-- A concrete SMT term is exactly the encoding of an intrinsic FO term. -/
def TermRepresentation {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) (target : STerm) : Prop :=
  target = term encoding source

/-- Existential package for a typed symbol declaration. -/
structure Declaration (symbols : FO.SymbolFamily) where
  declaration : FO.SymbolDecl
  symbol : symbols declaration

/-- Emit the ordinary concrete declaration selected for one typed symbol.
Callers establish that the symbol is not owned by a native command. -/
def declaration {symbols : FO.SymbolFamily} (encoding : Encoding symbols)
    (declared : Declaration symbols) : Command :=
  .declFun (encoding.name declared.symbol)
    (declared.declaration.args.map encoding.sort).toArray
    (encoding.sort declared.declaration.result)

mutual
  /-- All sorts occurring in a typed family term. -/
  def termSorts {symbols : FO.SymbolFamily} :
      {context : FO.Context} → {sort : FO.FOSort} →
        FO.FamilyTerm symbols context sort → List FO.FOSort
    | _, sort, .var _ => [sort]
    | _, _, .symbol (decl := decl) _ args =>
        decl.result :: decl.args ++ argumentSorts args
    | _, _, .boolLit _ => [.bool]
    | _, _, .not body => .bool :: termSorts body
    | _, _, .and left right | _, _, .or left right |
        _, _, .imp left right | _, _, .iff left right =>
      .bool :: termSorts left ++ termSorts right
    | _, _, .eq (sort := sort) left right =>
        [.bool, sort] ++ termSorts left ++ termSorts right
    | _, _, .forallE (domain := domain) body |
        _, _, .existsE (domain := domain) body =>
      [.bool, domain] ++ termSorts body

  /-- All sorts occurring in a typed argument telescope. -/
  def argumentSorts {symbols : FO.SymbolFamily} :
      {context : FO.Context} → {sorts : List FO.FOSort} →
        FO.FamilyArgs symbols context sorts → List FO.FOSort
    | _, _, .nil => []
    | _, _, .cons argument rest => termSorts argument ++ argumentSorts rest
end

/-- Stable first-occurrence list of the sorts used by declarations and formulas. -/
def usedSorts {symbols : FO.SymbolFamily}
    (declarations : List (Declaration symbols))
    (theory : FO.FamilyTheory symbols) : List FO.FOSort :=
  ((declarations.flatMap fun declared =>
      declared.declaration.args ++ [declared.declaration.result]) ++
    theory.flatMap termSorts).eraseDups

/-- Declare a represented sort exactly when it is a simple nullary SMT symbol.
Built-in, indexed, and compound sorts require no synthetic declaration here. -/
def sortDeclaration? {symbols : FO.SymbolFamily} (encoding : Encoding symbols)
    (sort : FO.FOSort) : Option Command :=
  match encoding.sort sort with
  | .app (.symb name) arguments =>
      if arguments.isEmpty then some (.declSort name 0) else none
  | _ => none

/-- Ordinary sorts not already declared by a native command. -/
def ordinarySorts {symbols : FO.SymbolFamily} (encoding : Encoding symbols)
    (declarations : List (Declaration symbols))
    (source : FO.FamilyTheory symbols) : List FO.FOSort :=
  (usedSorts declarations source).filter fun sort =>
    sort != .bool && !encoding.nativeSort sort

/-- Ordinary symbols not already declared by a native command. -/
def ordinaryDecls {symbols : FO.SymbolFamily} (encoding : Encoding symbols)
    (declarations : List (Declaration symbols)) : List (Declaration symbols) :=
  declarations.filter fun declared => !encoding.nativeSymbol declared.symbol

/-- The non-native suffix of the pure command encoder: remaining sort and symbol
declarations followed by assertions, each in stable source order. -/
def theoryBody {symbols : FO.SymbolFamily} (encoding : Encoding symbols)
    (declarations : List (Declaration symbols))
    (source : FO.FamilyTheory symbols) : Array Command :=
  ((ordinarySorts encoding declarations source).filterMap
      (sortDeclaration? encoding)).toArray ++
    ((ordinaryDecls encoding declarations).map (declaration encoding)).toArray ++
    (source.map fun formula => .assert (term encoding formula)).toArray

/-- Pure command encoder: native declarations followed by the ordinary body. -/
def theory {symbols : FO.SymbolFamily} (encoding : Encoding symbols)
    (declarations : List (Declaration symbols))
    (source : FO.FamilyTheory symbols) : Array Command :=
  encoding.nativeCommands ++ theoryBody encoding declarations source

@[simp] theorem native_sort_omitted {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols)
    (declarations : List (Declaration symbols))
    (source : FO.FamilyTheory symbols) (sort : FO.FOSort)
    (native : encoding.nativeSort sort = true) :
    sort ∉ ordinarySorts encoding declarations source := by
  simp [ordinarySorts, native]

@[simp] theorem native_decl_omitted {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) (declarations : List (Declaration symbols))
    (declared : Declaration symbols)
    (native : encoding.nativeSymbol declared.symbol = true) :
    declared ∉ ordinaryDecls encoding declarations := by
  simp [ordinaryDecls, native]

/-- A command sequence represents a typed theory when it is exactly the pure
encoding for some explicit ordered declaration trace. -/
def TheoryRepresentation {symbols : FO.SymbolFamily}
    (encoding : Encoding symbols) (source : FO.FamilyTheory symbols)
    (commands : Array Command) : Prop :=
  ∃ declarations : List (Declaration symbols),
    commands = theory encoding declarations source

/-- Convert the flattened translator's declaration package to the generic
representation package without changing order or symbol identity. -/
def ofDeclared {signature : Signature}
    (declared : DeclaredSymbol signature) : Declaration (Symbol signature) :=
  ⟨declared.declaration, declared.symbol⟩

/-- Commands produced by the pure specification encoder for one closed
flattened translation result. -/
def translatedBody {signature : Signature}
    (result : TranslationResult signature [] .bool) :
    TargetSentence signature :=
  result.term

/-- Complete theory carried by a closed flattened translation result. -/
def completeTheory {signature : Signature}
    (result : TranslationResult signature [] .bool) :
    TargetTheory signature :=
  result.theory ++ [translatedBody result]

/-- Commands produced by the pure specification encoder for one closed
flattened translation result. -/
def encode {signature : Signature} (encoding : Encoding (Symbol signature))
    (result : TranslationResult signature [] .bool) : Array Command :=
  theory encoding (result.declarations.map ofDeclared)
    (completeTheory result)

set_option quotPrecheck false

/-- Syntax brackets for the pure FO-to-SMT term encoder. -/
scoped notation:max "𝒶⟦" source "⟧[" encoding "]" => term encoding source

/-- The pure translation encoder represents the complete generated theory and
translated body by construction. -/
theorem encode_translation {signature : Signature}
    (encoding : Encoding (Symbol signature))
    (result : TranslationResult signature [] .bool) :
    TheoryRepresentation encoding (completeTheory result)
      (encode encoding result) :=
  ⟨result.declarations.map ofDeclared, rfl⟩

end Crush.Metatheory.SMT
