import Crush.Metatheory.Datatype.Semantics
import Crush.Metatheory.Datatype.Syntax
import Crush.Metatheory.Datatype.Model
import Crush.Metatheory.Datatype.Guarded
import Crush.Metatheory.Datatype.Carrier
import Crush.Metatheory.Reification.Datatype
import Crush.Metatheory.Reification.Reify
import Crush.Metatheory.Reification.Witness
import Crush.Metatheory.SMT.Datatype
import Crush.Metatheory.SMT.DatatypeTransport
import Crush.Metatheory.SMT.DatatypeGuard
import Crush.Metatheory.SMT.DatatypeRepresentation
import Crush.Metatheory.SMT.Soundness
import Crush.Metatheory.SMT.Semantics
import Crush.Metatheory.VCG.CommandEquivalence
import Crush.Frontend.Tactic

/-!
# Datatype metatheory tests

These examples exercise canonical datatype structure without using Lean
declaration metadata, raw SMT syntax, or a solver.
-/

namespace Crush.Metatheory.Datatype.Tests

private def int : BaseSort := ⟨"Int"⟩
private abbrev IntBase : BaseSort → Type := fun _ => Int

/-! ## A monomorphic option -/

private abbrev valueField : FieldDecl 1 :=
  { name := "value", sort := .base int }

private def noneCtor : CtorDecl 1 :=
  { name := "none", fields := [] }

private def someCtor : CtorDecl 1 :=
  { name := "some", fields := [valueField] }

private def optionDecl : DataDecl 1 :=
  { sort := ⟨"Option_Int"⟩, ctors := [noneCtor, someCtor] }

private def optionBlock : Block 1 :=
  { decl := fun _ => optionDecl }

private def optionData : DataRef optionBlock := 0
private def noneRef : CtorRef optionBlock optionData noneCtor := .here
private def someRef : CtorRef optionBlock optionData someCtor := .there .here
private def valueRef : FieldRef someCtor valueField := .here

example : optionBlock.wellFormed = true := by decide
example : optionBlock.productive = true := by decide

example : someCtor.ty optionBlock optionData =
    .arrow (.base int) (.base optionDecl.sort) := rfl

example : someCtor.fo optionBlock optionData =
    { args := [.base int], result := .base optionDecl.sort } := rfl

example : valueField.sel optionBlock optionData =
    { args := [.base optionDecl.sort], result := .base int } := rfl

example : someCtor.test optionBlock optionData =
    { args := [.base optionDecl.sort], result := .bool } := rfl

private def optionEncoding : Crush.Metatheory.SMT.Datatype.BlockEncoding 1 where
  name
    | .sort _ => "Option_Int"
    | .ctor _ 0 => "Option_Int_none"
    | .ctor _ _ => "Option_Int_some"
    | .sel _ _ _ => "Option_Int_some_0"
  baseSort := fun _ => .app (.symb "Int") #[]

example : Crush.Metatheory.SMT.Datatype.command optionBlock optionEncoding =
    .declDatatypes #[
      ("Option_Int", 0, {
        params := #[]
        ctors := #[
          { name := "Option_Int_none", selDecls := #[] },
          { name := "Option_Int_some",
            selDecls := #[("Option_Int_some_0", .app (.symb "Int") #[])] }
        ]
      })
    ] := rfl

example : Crush.SMT.DatatypesSupported
    (Crush.Metatheory.SMT.Datatype.entries optionBlock optionEncoding) := by
  simp [Crush.SMT.DatatypesSupported, Crush.SMT.datatypeSymbols,
    Crush.SMT.datatypeCtors, Crush.SMT.CtorDecl.tester,
    Crush.Metatheory.SMT.Datatype.entries,
    Crush.Metatheory.SMT.Datatype.dataDecl,
    Crush.Metatheory.SMT.Datatype.ctorDecl, optionBlock, optionDecl,
    noneCtor, someCtor, valueField, optionEncoding,
    Crush.Metatheory.SMT.Datatype.fieldSort] <;> grind

example : ¬Crush.SMT.DatatypesSupported #[] := by
  simp [Crush.SMT.DatatypesSupported]

example : ¬Crush.SMT.DatatypesSupported #[
    ("Bad", 0, { params := #[], ctors := #[] })] := by
  simp [Crush.SMT.DatatypesSupported]

private def rawTree : Array (String × Nat × Crush.SMT.DatatypeDecl) := #[
  ("Tree", 0, { ctors := #[
    { name := "leaf", selDecls := #[] },
    { name := "node", selDecls := #[
      ("left", .app (.symb "Tree") #[]),
      ("right", .app (.symb "Tree") #[])] }] })]

example : Crush.SMT.DatatypesSupported rawTree := by
  simp [Crush.SMT.DatatypesSupported, Crush.SMT.datatypeSymbols,
    Crush.SMT.datatypeCtors, Crush.SMT.CtorDecl.tester, rawTree] <;> grind

private def rawMutual : Array (String × Nat × Crush.SMT.DatatypeDecl) := #[
  ("Tree", 0, { ctors := #[
    { name := "leaf", selDecls := #[] },
    { name := "node", selDecls := #[
      ("children", .app (.symb "Trees") #[])] }] }),
  ("Trees", 0, { ctors := #[
    { name := "nil", selDecls := #[] },
    { name := "cons", selDecls := #[
      ("head", .app (.symb "Tree") #[]),
      ("tail", .app (.symb "Trees") #[])] }] })]

example : Crush.SMT.DatatypesSupported rawMutual := by
  simp [Crush.SMT.DatatypesSupported, Crush.SMT.datatypeSymbols,
    Crush.SMT.datatypeCtors, Crush.SMT.CtorDecl.tester, rawMutual] <;> grind

private def duplicateCtor : Array (String × Nat × Crush.SMT.DatatypeDecl) := #[
  ("Left", 0, { ctors := #[{ name := "mk", selDecls := #[] }] }),
  ("Right", 0, { ctors := #[{ name := "mk", selDecls := #[] }] })]

example : ¬Crush.SMT.DatatypesSupported duplicateCtor := by
  simp [Crush.SMT.DatatypesSupported, Crush.SMT.datatypeSymbols,
    Crush.SMT.datatypeCtors, Crush.SMT.CtorDecl.tester, duplicateCtor]

example : ¬Crush.SMT.DatatypesSupported #[
    ("Parametric", 1, {
      params := #["α"]
      ctors := #[{ name := "mk", selDecls := #[] }] })] := by
  simp [Crush.SMT.DatatypesSupported]

private def rawWFDef : Crush.SMT.FunDef := {
  name := "wf_Tree"
  args := #[("value", .app (.symb "Tree") #[])]
  resSort := Crush.SMT.boolSort
  body := .bvar 0 }

private def rawValue : Crush.SMT.Term := .bvar 0
private def rawGuard : Crush.SMT.Term :=
  .app (.symb "guard") #[.app (.symb "value") #[rawValue]]
private def rawTester : Crush.SMT.Term :=
  .app (.indexed "is" #[.inl "some"]) #[rawValue]

example : SMT.Datatype.wfBody
    #[("none", #[]), ("some", #[rawGuard])] rawValue =
      (smt| (=> $rawTester $rawGuard)) := rfl

example : Crush.SMT.FunsRecSupported #[rawWFDef] := by
  refine ⟨by simp, by simp [rawWFDef], ?_⟩
  intro definition member
  have equal : definition = rawWFDef := by simpa using member
  subst definition
  exact .symb _ (by decide) (by decide) (by decide) (by decide) (by decide)

example : ¬Crush.SMT.FunsRecSupported #[] := by
  simp [Crush.SMT.FunsRecSupported]

example : ¬Crush.SMT.FunsRecSupported #[rawWFDef, rawWFDef] := by
  simp [Crush.SMT.FunsRecSupported, rawWFDef]

private def none : Val optionBlock IntBase optionData :=
  mk noneRef .nil

private def some (value : Int) : Val optionBlock IntBase optionData :=
  mk someRef (.base value .nil)

example : none ≠ some 3 := by
  exact ctor_ne noneRef someRef (by decide) .nil (.base 3 .nil)

example : IsCtor noneRef none := test_ctor noneRef .nil

example : ¬IsCtor noneRef (some 3) := by
  exact test_ne noneRef someRef (by decide) (.base 3 .nil)

example : sel (Base := IntBase) someRef valueRef (0 : Int) (some 7) = (7 : Int) := by
  exact sel_ctor (Base := IntBase) someRef valueRef (0 : Int) (.base 7 .nil)

private theorem option_productive : Productive optionBlock := by
  intro data
  have equal : data = optionData := Subsingleton.elim _ _
  subst data
  exact ⟨mk noneRef .nil⟩

private theorem option_wf : optionBlock.WF := by
  exact (Block.wellFormed_eq_true optionBlock).mp (by decide)

private def liftedSome : BaseLift optionBlock IntBase optionDecl.sort :=
  .data optionData rfl (some 7)

private abbrev intCarriers : FO.Carriers where
  Base := IntBase
  Fn := fun _ _ => Unit
  baseNonempty := fun _ => inferInstance
  fnNonempty := fun _ _ => inferInstance

private theorem int_external (dataRef : DataRef optionBlock) :
    dataRef.decl.sort ≠ int := by
  have equal : dataRef = optionData := Subsingleton.elim _ _
  subst dataRef
  decide

/-- The enlarged datatype carrier contains the complete free value, rather
than only values reached by decoding a source constructor application. -/
example : liftedSome.asData option_wf optionData = some 7 := rfl

example : BaseLift.data optionData rfl
    (liftedSome.asData option_wf optionData) = liftedSome := by
  exact BaseLift.data_asData option_wf optionData liftedSome

/-- Native constructors range over the entire enlarged field carrier: the
ill-formed negative payload exists and is later excluded only by `wf_T`. -/
example : BaseLift.targetCtor option_wf option_productive intCarriers someRef
      (.external int_external (-1)) =
    (.data optionData rfl (some (-1)) :
      BaseLift optionBlock IntBase optionDecl.sort) := rfl

example : Nonempty (Val optionBlock IntBase optionData) :=
  val_nonempty option_productive (fun _ => inferInstance) optionData

/-! The guarded lifting is block-generic: this option instance is derived from
the same construction used for recursive and mutual datatypes. -/

private abbrev NatBase : BaseSort → Type := fun _ => Nat

private def natBase : Guarded.BaseRepresentations NatBase IntBase :=
  fun _ => Guarded.natInt.representation

private abbrev NoSymbols : FO.SymbolFamily := fun _ => Empty

private def natFamily : FO.FamilyModel NoSymbols where
  carriers := {
    Base := NatBase
    Fn := fun _ _ => Unit
    baseNonempty := fun _ => inferInstance
    fnNonempty := fun _ _ => inferInstance }
  symbol := fun symbol => nomatch symbol

/-- The initial interpreted model changes every opaque base carrier from `Nat`
to `Int`, while retaining a full source-to-target model relation. -/
private noncomputable def natPrior : Lifted natFamily :=
  Lifted.ofBase natFamily natBase

example : (natPrior.relation (.base int)).encode (3 : Nat) = (3 : Int) := rfl

example : ¬(natPrior.relation (.base int)).guard (-1 : Int) := by
  change ¬(0 : Int) ≤ -1
  omega

example : FO.ModelRel natFamily natPrior.target natPrior.relation :=
  natPrior.models

private def someNat (value : Nat) : Val optionBlock NatBase optionData :=
  mk someRef (.base value .nil)

private noncomputable def guardedOption :=
  lift natBase option_productive optionData

example (value : Val optionBlock NatBase optionData) :
    guardedOption.decode (guardedOption.encode value)
      (guardedOption.encode_guard value) = value :=
  guardedOption.decode_encode value

example : ¬guardedOption.guard (some (-1)) := by
  simp [guardedOption, lift, some, Val.WF, Args.WF, natBase,
    Guarded.natInt]

example : guardedOption.encode (someNat 7) = some 7 := rfl

/-- The Crush translator's tester/selector-shaped guard denotes the same subset as the
canonical structural predicate. -/
example (value : Val optionBlock IntBase optionData) :
    value.WF (fun sort => (natBase sort).guard) ↔
      value.SelWF (fun sort => (natBase sort).guard) :=
  value.wf_iff_selWF natBase option_productive

/-! ## A directly recursive tree -/

private abbrev leafField : FieldDecl 1 :=
  { name := "value", sort := .base int }

private def leftField : FieldDecl 1 :=
  { name := "left", sort := .data 0 }

private def rightField : FieldDecl 1 :=
  { name := "right", sort := .data 0 }

private def leafCtor : CtorDecl 1 :=
  { name := "leaf", fields := [leafField] }

private def nodeCtor : CtorDecl 1 :=
  { name := "node", fields := [leftField, rightField] }

private def treeDecl : DataDecl 1 :=
  { sort := ⟨"Tree_Int"⟩, ctors := [leafCtor, nodeCtor] }

private def treeBlock : Block 1 :=
  { decl := fun _ => treeDecl }

private def treeData : DataRef treeBlock := 0
private def leafRef : CtorRef treeBlock treeData leafCtor := .here
private def nodeRef : CtorRef treeBlock treeData nodeCtor := .there .here

private def leaf (value : Int) : Val treeBlock IntBase treeData :=
  mk leafRef (.base value .nil)

private def node (left right : Val treeBlock IntBase treeData) :
    Val treeBlock IntBase treeData :=
  mk nodeRef (.data left (.data right .nil))

example : IsCtor nodeRef (node (leaf 1) (leaf 2)) :=
  test_ctor nodeRef (.data (leaf 1) (.data (leaf 2) .nil))

example : (leaf 1).height = 1 := rfl
example : (node (leaf 1) (leaf 2)).height = 2 := rfl

private theorem tree_productive : Productive treeBlock := by
  intro data
  have equal : data = treeData := Subsingleton.elim _ _
  subst data
  exact ⟨mk leafRef (.base () .nil)⟩

private def leafNat (value : Nat) : Val treeBlock NatBase treeData :=
  mk leafRef (.base value .nil)

private noncomputable def guardedTree :=
  lift natBase tree_productive treeData

example : guardedTree.encode (leafNat 3) = leaf 3 := rfl

example : ¬guardedTree.guard (node (leaf 1) (leaf (-1))) := by
  simp [guardedTree, lift, node, leaf, Val.WF, Args.WF, natBase,
    Guarded.natInt]

/-- The same selector characterization is block-generic and therefore covers
recursive guarded fields rather than only the `Option` case. -/
example (value : Val treeBlock IntBase treeData) :
    value.WF (fun sort => (natBase sort).guard) ↔
      value.SelWF (fun sort => (natBase sort).guard) :=
  value.wf_iff_selWF natBase tree_productive

example : Nonempty (Val treeBlock IntBase treeData) :=
  val_nonempty tree_productive (fun _ => inferInstance) treeData

example : treeBlock.productive = true := by decide

/-! ## One mutually recursive block -/

private def treeListField : FieldDecl 2 :=
  { name := "children", sort := .data 1 }

private def mutualLeaf : CtorDecl 2 :=
  { name := "leaf", fields := [] }

private def mutualNode : CtorDecl 2 :=
  { name := "node", fields := [treeListField] }

private def headField : FieldDecl 2 :=
  { name := "head", sort := .data 0 }

private def tailField : FieldDecl 2 :=
  { name := "tail", sort := .data 1 }

private def nilCtor : CtorDecl 2 :=
  { name := "nil", fields := [] }

private def consCtor : CtorDecl 2 :=
  { name := "cons", fields := [headField, tailField] }

private def mutualTreeDecl : DataDecl 2 :=
  { sort := ⟨"Tree"⟩, ctors := [mutualLeaf, mutualNode] }

private def mutualTreesDecl : DataDecl 2 :=
  { sort := ⟨"Trees"⟩, ctors := [nilCtor, consCtor] }

private def mutualBlock : Block 2 :=
  { decl := Fin.cases mutualTreeDecl (fun _ => mutualTreesDecl) }

private def mutualTree : DataRef mutualBlock := 0
private def mutualTrees : DataRef mutualBlock := 1

private def mutualLeafRef :
    CtorRef mutualBlock mutualTree mutualLeaf := .here

private def nilRef : CtorRef mutualBlock mutualTrees nilCtor := .here

private theorem mutual_productive : Productive mutualBlock := by
  intro data
  refine Fin.cases ?_ (fun tail => ?_) data
  · exact ⟨mk mutualLeafRef .nil⟩
  · have equal : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    exact ⟨mk nilRef .nil⟩

example : Nonempty (Val mutualBlock IntBase mutualTree) :=
  val_nonempty mutual_productive (fun _ => inferInstance) mutualTree

example : Nonempty (Val mutualBlock IntBase mutualTrees) :=
  val_nonempty mutual_productive (fun _ => inferInstance) mutualTrees

example : mutualBlock.productive = true := by decide

/-! ## A constructor-only block can still be uninhabited -/

private def loopField : FieldDecl 1 :=
  { name := "next", sort := .data 0 }

private def loopCtor : CtorDecl 1 :=
  { name := "mk", fields := [loopField] }

private def loopDecl : DataDecl 1 :=
  { sort := ⟨"Loop"⟩, ctors := [loopCtor] }

private def loopBlock : Block 1 :=
  { decl := fun _ => loopDecl }

example : loopBlock.wellFormed = true := by decide
example : loopBlock.productive = false := by decide

/-! A field cannot be labeled external while reusing the sort identity of the
current datatype block. Recursive fields must use `.data`. -/

private def disguisedField : FieldDecl 1 :=
  { name := "next", sort := .base ⟨"Disguised"⟩ }

private def disguisedBlock : Block 1 :=
  { decl := fun _ =>
      { sort := ⟨"Disguised"⟩
        ctors := [{ name := "mk", fields := [disguisedField] }] } }

example : disguisedBlock.wellFormed = false := by decide

end Crush.Metatheory.Datatype.Tests

/-! ## Composed SMT datatype soundness API -/

namespace Crush.Metatheory.SMT.Datatype.Tests

open Crush.Metatheory.Datatype
open Crush.Metatheory.Defunctionalization.Flattened
open Crush.Metatheory.VCG
open scoped Crush.Metatheory Crush.SMT

variable {signature : Signature} {n : Nat} {block : Block n}
variable {symbols : Symbols signature block} {source : Model signature}
variable {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding n}

example (freeDataModel : IsFreeDatatypeModel symbols source)
    (represented : Representation block symbols fo data) :
    (SMT.model fo (canonicalModel source)).SatisfiesCommand
      (command block data) :=
  command_sound freeDataModel represented

/-- Additional derived graphs compose with the same FO representation: ordinary
symbols and assertions remain valid by disjointness. -/
example (extra : SMT.ExtraGraph fo (canonicalModel source))
    (formula : Sentence signature) {commands : Array Crush.SMT.Command}
    (encoded : SMT.TheoryRepresentation fo (translatedTheory formula) commands)
    (valid : canonicalModel source ⊨ᵀ translatedTheory formula)
    (datatypeCommandsValid : SMT.modelWith fo (canonicalModel source) extra ⊨ₛᶜ
      fo.nativeCommands) :
    ∃ smtModel, smtModel ⊨ₛᶜ commands :=
  SMT.lift_with_extra fo encoded (canonicalModel source) valid extra datatypeCommandsValid

/-- The ordinary case uses the same theorem with an empty environment. -/
example (empty : fo.nativeCommands = #[]) (formula : Sentence signature)
    {commands : Array Crush.SMT.Command}
    (encoded : SMT.TheoryRepresentation fo (translatedTheory formula) commands)
    (valid : canonicalModel source ⊨ᵀ translatedTheory formula) :
    ∃ smtModel, smtModel ⊨ₛᶜ commands :=
  SMT.representation_sound fo (.nil fo empty) encoded source .nil valid

example {env : Datatype.Env signature} (represented : EnvRepresentation fo env)
    (formula : Sentence signature) {commands : Array Crush.SMT.Command}
    (encoded : SMT.TheoryRepresentation fo (translatedTheory formula) commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    Datatype.Env.Unsatisfiable env formula :=
  SMT.commands_unsat_implies_source_unsat fo represented formula encoded unsat

/-- Dependency-ordered blocks assemble into one guarded target and one model
relation for the complete flattened symbol family. -/
example {env : Datatype.Env signature} (represented : EnvRepresentation fo env)
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source env) :
    FO.ModelRel (canonicalModel source)
      (represented.lifted source freeDataModel).target
      (represented.lifted source freeDataModel).relation :=
  (represented.lifted source freeDataModel).models

/-- Every earlier SMT datatype declaration survives the complete dependency fold when
the representation records the cross-block ordering condition. -/
example {env : Datatype.Env signature} (represented : EnvRepresentation fo env)
    (ordered : Native.ModelExtension.DependencyOrdered represented.blocks)
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source env) :
    (SMT.model fo (represented.lifted source freeDataModel).target).SatisfiesCommands
      fo.nativeCommands :=
  represented.lifted_valid ordered source freeDataModel

/-- Fresh derived graphs, including the combined integer/datatype-guard graph,
do not disturb the SMT datatype prefix. -/
example {env : Datatype.Env signature} (represented : EnvRepresentation fo env)
    (ordered : Native.ModelExtension.DependencyOrdered represented.blocks)
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source env)
    (extra : SMT.ExtraGraph fo (represented.lifted source freeDataModel).target) :
    (SMT.modelWith fo (represented.lifted source freeDataModel).target extra).SatisfiesCommands
      fo.nativeCommands :=
  represented.lifted_valid_with ordered source freeDataModel extra

/-- The guarded target uses the same complete representation theorem rather
than a datatype-only soundness path. -/
example {env : Datatype.Env signature} (represented : EnvRepresentation fo env)
    (ordered : Native.ModelExtension.DependencyOrdered represented.blocks)
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source env)
    {theory : FO.FamilyTheory (Symbol signature)}
    {commands : Array Crush.SMT.Command}
    (encoded : SMT.TheoryRepresentation fo theory commands)
    (extra : SMT.ExtraGraph fo (represented.lifted source freeDataModel).target)
    (valid : (represented.lifted source freeDataModel).target.SatisfiesTheory theory) :
    ∃ model : Crush.SMT.Model, model.SatisfiesCommands commands :=
  represented.sound_with ordered encoded source freeDataModel extra valid

/-- Interpreted carriers enter before datatype blocks and then use the same
whole-theory theorem. This is the route used by guarded `Nat → Int` fields. -/
example {env : Datatype.Env signature} (represented : EnvRepresentation fo env)
    (ordered : Native.ModelExtension.DependencyOrdered represented.blocks)
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source env)
    (prior : Lifted (canonicalModel source))
    {theory : FO.FamilyTheory (Symbol signature)}
    {commands : Array Crush.SMT.Command}
    (encoded : SMT.TheoryRepresentation fo theory commands)
    (extra : SMT.ExtraGraph fo
      (represented.liftedFrom source freeDataModel prior).target)
    (valid : (represented.liftedFrom source freeDataModel prior).target.SatisfiesTheory
      theory) :
    ∃ model : Crush.SMT.Model, model.SatisfiesCommands commands :=
  represented.soundFrom ordered encoded source freeDataModel prior extra valid

/-- A translation fact enters the existing shared soundness API
through one representation boundary; no datatype-only solver theorem is added. -/
example (translation : FactTranslationRecord)
    (encoding : SMT.Encoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (locations : translation.datatypeDeclarationLocations.Representation encoding)
    (native : encoding.nativeCommands = translation.datatypeDeclarations) :
    EnvRepresentation encoding translation.datatypeSignaturePrefix.toModelEnv :=
  ({ declarations := locations, datatypeDeclarations_eq := native } :
    translation.Representation encoding).datatypeRepresentation

/-- Command equivalence follows semantic command-set equality: declaration
and assertion interleaving plus duplicate elimination do not change which
untyped SMT models satisfy the commands. -/
private def commandA : Crush.SMT.Command := .declSort "A" 0
private def commandB : Crush.SMT.Command := .assert (smt| true)

example : sameCommandSet? #[commandA, commandB]
    #[commandB, commandA, commandB] = true := by native_decide

example : sameCommandSet? #[commandA] #[commandA, commandB] = false := by
  native_decide

/-- The single-fact theorem is indexed by the retained source fact and final
command array. Root-level `:named` annotations are removed only through the
semantic transparency theorem above. -/
example (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented) :
    Option (SomeFactCommandRepresentation translation guarding represented guarded) :=
  FactCommandRepresentation.build?

example (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    {expressions : List Lean.Expr}
    (reified : Reification.ReifiedSentencesFor translation.datatypes
      translation.constants expressions) :
    Option (PLift (SMT.GuardedTheoryRepresentation guarding
      translation.guardDefinitionCommands (translatedTheories reified.sources)
      (translation.emittedCommands.map stripAssertionAnnotation))) :=
  CommandEquivalence.build? reified

example (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (reified : Reification.ReifiedSentenceFor translation.expression translation.datatypes
      translation.constants)
    (representation : FactCommandRepresentation translation guarding represented guarded
      reified)
    (interpretation : translation.GuardDefinitionSemantics guarding represented guarded)
    (unsat : Crush.SMT.CommandsUnsatisfiable translation.emittedCommands) :
    Datatype.Env.Unsatisfiable translation.datatypeSignaturePrefix.toModelEnv reified.source :=
  representation.unsat_source interpretation unsat

/-- The leading `set-logic` command returned by `buildScript` is accounted for
by semantic equivalence rather than silently dropped. -/
example (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (reified : Reification.ReifiedSentenceFor translation.expression translation.datatypes
      translation.constants)
    (representation : FactCommandRepresentation translation guarding represented guarded
      reified)
    (interpretation : translation.GuardDefinitionSemantics guarding represented guarded)
    (logic : String)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (#[.setLogic logic] ++ translation.emittedCommands)) :
    Datatype.Env.Unsatisfiable translation.datatypeSignaturePrefix.toModelEnv reified.source :=
  representation.unsat_source_script interpretation logic unsat

end Crush.Metatheory.SMT.Datatype.Tests

/-! ## Executable Lean declaration reification -/

namespace Crush.Metatheory.Reification.Tests

open Lean Meta
open Crush (datatypePlan)

inductive ReifiedTree (α : Type) where
  | leaf : α → ReifiedTree α
  | node : ReifiedTree α → ReifiedTree α → ReifiedTree α

mutual
  inductive ReifiedMutualTree where
    | leaf : ReifiedMutualTree
    | node : ReifiedMutualTrees → ReifiedMutualTree
  inductive ReifiedMutualTrees where
    | nil : ReifiedMutualTrees
    | cons : ReifiedMutualTree → ReifiedMutualTrees → ReifiedMutualTrees
end

inductive ReifiedLoop where
  | next : ReifiedLoop → ReifiedLoop

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem nonproductive_not_nonempty
    (allFalse : ∀ value : ReifiedLoop, False) : False := by
  crush

inductive ReifiedFnBox where
  | mk : (Int → Int) → ReifiedFnBox

inductive ReifiedProofBox : Type where
  | mk : (0 = 0) → ReifiedProofBox

inductive ReifiedDependent where
  | mk (size : Nat) (value : Fin (size + 1))

inductive ReifiedIndexed (α : Type) : Nat → Type where
  | zero : ReifiedIndexed α 0

inductive ReifiedProp : Prop where
  | intro

inductive ReifiedEmpty

inductive ReifiedRose where
  | node : List ReifiedRose → ReifiedRose

structure ReifiedPoint where
  x : Int
  y : Int

structure ReifiedNatBox where
  value : Nat

class ReifiedClass where
  value : Int

private def reifiedRecursorFormula : Prop :=
  ∀ value : Option Int,
    Option.casesOn value True (fun _ => True)

private def reifiedQuotFormula : Prop :=
  ∀ value : Quot (fun _ _ : Int => True), value = value

namespace DatatypeNameCollision

inductive Bool where
  | mk

end DatatypeNameCollision

run_meta do
  let int := mkConst ``Int
  let optionPlan ← datatypePlan ``Option #[int]
  let some optionMember := optionPlan.members[0]?
    | throwError "datatype declaration planning lost `Option Int`"
  let some someCtor := optionMember.ctors[1]?
    | throwError "datatype declaration planning lost `Option.some`"
  unless optionPlan.members.size == 1 && optionMember.ctors.size == 2 &&
      someCtor.fields.size == 1 do
    throwError "datatype declaration planning lost `Option Int` structure"
  let mutualPlan ← datatypePlan ``ReifiedMutualTree #[]
  unless mutualPlan.members.size == 2 do
    throwError "datatype declaration planning split a mutual block"
  let some option ← reifyDatatypeBlock? ``Option #[int]
    | throwError "datatype reification rejected `Option Int`"
  unless option.arity == 1 && option.names == #[``Option] do
    throwError "datatype reification lost the `Option Int` block identity"
  let some optionData := option.find? ``Option
    | throwError "datatype reification lost the `Option` datatype reference"
  unless (option.block.decl optionData).ctors.length == 2 do
    throwError "datatype reification lost `Option` constructor order"
  match ← reifyDatatypeApp ``Option #[int] with
  | .error reason =>
      throwError "shared datatype acceptance rejected `Option Int`: {repr reason}"
  | .ok accepted =>
      unless accepted.env.blocks.size == 1 && accepted.data.val == 0 do
        throwError "shared datatype acceptance lost the selected declaration"
  match ← reifyDatatypeApp ``Option #[] with
  | .error (.parameters ``Option) => pure ()
  | .error reason => throwError "wrong missing-parameter rejection: {repr reason}"
  | .ok _ => throwError "datatype acceptance omitted a required type parameter"
  let some tree ← reifyDatatypeBlock? ``ReifiedTree #[int]
    | throwError "datatype reification rejected a direct recursive tree"
  unless tree.block.productive do
    throwError "a reified recursive tree was not constructively productive"
  let some mutualTree ← reifyDatatypeBlock? ``ReifiedMutualTree #[]
    | throwError "datatype reification rejected a direct mutual block"
  unless mutualTree.arity == 2 && mutualTree.names.size == 2 do
    throwError "datatype reification lost the mutual declaration block"
  if (← reifyDatatypeBlock? ``ReifiedLoop #[]).isSome then
    throwError "datatype reification accepted a nonproductive recursive carrier"
  if (← reifyDatatypeBlock? ``ReifiedFnBox #[]).isSome then
    throwError "datatype reification accepted a function-valued field"
  if (← reifyDatatypeBlock? ``ReifiedProofBox #[]).isSome then
    throwError "datatype reification accepted a proof-valued field"
  if (← reifyDatatypeBlock? ``ReifiedDependent #[]).isSome then
    throwError "datatype reification accepted a dependent constructor field"
  if (← reifyDatatypeBlock? ``ReifiedProp #[]).isSome then
    throwError "datatype reification accepted a Prop-valued inductive"
  if (← reifyDatatypeBlock? ``ReifiedEmpty #[]).isSome then
    throwError "datatype reification accepted an empty inductive"
  if (← reifyDatatypeBlock? ``Vector #[int]).isSome then
    throwError "datatype reification accepted an indexed family"
  match ← reifyDatatypeEnv #[mkConst ``ReifiedFnBox] with
  | .error (.functionField ``ReifiedFnBox.mk 0) => pure ()
  | .error reason => throwError "wrong function-field rejection: {repr reason}"
  | .ok _ => throwError "environment accepted a function-valued field"
  match ← reifyDatatypeEnv #[mkConst ``ReifiedProofBox] with
  | .error (.proofField ``ReifiedProofBox.mk 0) => pure ()
  | .error reason => throwError "wrong proof-field rejection: {repr reason}"
  | .ok _ => throwError "environment accepted a proof-valued field"
  match ← reifyDatatypeEnv #[mkConst ``ReifiedDependent] with
  | .error (.dependentField ``ReifiedDependent.mk 1) => pure ()
  | .error reason => throwError "wrong dependent-field rejection: {repr reason}"
  | .ok _ => throwError "environment accepted a dependent field"
  match ← reifyDatatypeEnv #[mkConst ``ReifiedProp] with
  | .error (.prop ``ReifiedProp) => pure ()
  | .error reason => throwError "wrong Prop-inductive rejection: {repr reason}"
  | .ok _ => throwError "environment accepted a Prop inductive"
  match ← reifyDatatypeEnv #[mkConst ``ReifiedEmpty] with
  | .error (.empty ``ReifiedEmpty) => pure ()
  | .error reason => throwError "wrong empty-inductive rejection: {repr reason}"
  | .ok _ => throwError "environment accepted an empty inductive"
  match ← reifyDatatypeEnv #[mkConst ``ReifiedClass] with
  | .error (.typeclass ``ReifiedClass) => pure ()
  | .error reason => throwError "wrong typeclass rejection: {repr reason}"
  | .ok _ => throwError "environment accepted a typeclass as a datatype"
  let indexed ← mkConstWithFreshMVarLevels ``ReifiedIndexed
  match ← reifyDatatypeEnv #[mkApp indexed int] with
  | .error (.indexed ``ReifiedIndexed) => pure ()
  | .error reason => throwError "wrong indexed-family rejection: {repr reason}"
  | .ok _ => throwError "environment accepted an indexed family"
  let optionHead ← mkConstWithFreshMVarLevels ``Option
  let optionInt := mkApp optionHead int
  let optionOptionInt := mkApp optionHead optionInt
  match ← reifyDatatypeEnv #[optionOptionInt] with
  | .error reason =>
      throwError "nested datatype environment reification failed: {repr reason}"
  | .ok env =>
      unless env.blocks.size == 2 do
        throwError "nested datatype dependencies were not collected separately"
      let sorts := env.sorts.map (·.name)
      unless sorts.length == 2 && sorts.Nodup do
        throwError "nested monomorphic datatype identities were conflated"
  let bool := mkConst ``Bool
  let optionBool := mkApp optionHead bool
  match ← reifyDatatypeEnv #[optionInt, optionBool] with
  | .error reason =>
      throwError "distinct datatype instantiations failed: {repr reason}"
  | .ok env =>
      unless env.blocks.size == 2 && env.sorts.Nodup do
        throwError "`Option Int` and `Option Bool` were not kept distinct"
  let reflexiveSentence (type : Expr) (name : Name) : MetaM Expr :=
    withLocalDeclD name type fun value => do
      let equality ← mkEq value value
      mkForallFVars #[value] equality
  let pointSentence ← reflexiveSentence (mkConst ``ReifiedPoint) `point
  let treeSentence ← reflexiveSentence
    (mkApp (mkConst ``ReifiedTree) int) `tree
  let commonExpressions := #[pointSentence, treeSentence]
  let some (.pack commonEnv _ commonSentences) ←
      reifyTheory? commonExpressions
    | throwError "common theory reification rejected two supported facts"
  unless commonEnv.containsHead ``ReifiedPoint &&
      commonEnv.containsHead ``ReifiedTree do
    throwError "common theory reification did not retain both datatype blocks"
  unless commonSentences.sources.length == commonExpressions.size do
    throwError "common theory reification reordered or dropped a source fact"
  let loop := mkConst ``ReifiedLoop
  match ← reifyDatatypeEnv #[loop] with
  | .error (.nonproductive _) => pure ()
  | .error reason => throwError "wrong nonproductive rejection: {repr reason}"
  | .ok _ => throwError "environment collection accepted an empty recursive carrier"
  let rose := mkConst ``ReifiedRose
  match ← reifyDatatypeEnv #[rose] with
  | .error (.cyclic _) => pure ()
  | .error reason => throwError "wrong indirect-recursion rejection: {repr reason}"
  | .ok _ => throwError "environment collection accepted cross-block recursion"

  let recursorInfo ← getConstInfoDefn ``reifiedRecursorFormula
  match ← reifyDataSignature recursorInfo.value with
  | .error (.recursor ``Option.casesOn) => pure ()
  | .error reason => throwError "wrong datatype-recursor rejection: {repr reason}"
  | .ok _ => throwError "datatype signature accepted an unsupported recursor"
  let recursorFact : Crush.Fact := {
    prop := recursorInfo.value
    proof := none
    descr := "unsupported datatype recursor" }
  let (_, recursorState) ← Crush.buildScript
    { certifyDatatype := true } #[recursorFact]
  unless recursorState.trustReasons.any fun
      | .datatype (.recursor ``Option.casesOn) => true
      | _ => false do
    throwError "translation fallback lost the datatype-recursor rejection"
  let quotInfo ← getConstInfoDefn ``reifiedQuotFormula
  match ← reifyDataSignature quotInfo.value with
  | .error (.quotient ``Quot) => pure ()
  | .error reason => throwError "wrong quotient rejection: {repr reason}"
  | .ok _ => throwError "datatype signature accepted quotient primitives"
  let quotFact : Crush.Fact := {
    prop := quotInfo.value
    proof := none
    descr := "unsupported quotient" }
  let (_, quotState) ← Crush.buildScript { certifyDatatype := true } #[quotFact]
  unless quotState.trustReasons.any fun
      | .datatype (.quotient ``Quot) => true
      | _ => false do
    throwError "translation fallback lost the quotient rejection"

  let pointMk := mkConst ``ReifiedPoint.mk
  let pointX := mkConst ``ReifiedPoint.x
  withLocalDeclD `x int fun x => do
    withLocalDeclD `y int fun y => do
      let built := mkApp2 pointMk x y
      let projected := mkApp pointX built
      let equal := mkApp3 (mkConst ``Eq [1]) int projected x
      let sentence ← mkForallFVars #[x, y] equal
      match ← reifyDataSignature sentence with
      | .error reason =>
          throwError "datatype-aware signature rejected a point: {repr reason}"
      | .ok (.pack data tail) =>
          unless data.containsHead ``ReifiedPoint do
            throwError "datatype-aware signature omitted `ReifiedPoint`"
          let signature := tail.prepend data.signature
          let datatypePrefix := DatatypeSignaturePrefix.of data _
          unless (← reifyTerm? signature ReifiedContext.nil sentence
              (some datatypePrefix)).isSome do
            throwError "exact constructor/projection reification rejected a point"
          let some certified ← reifySentence? sentence
            | throwError "sentence witness rejected a certified point"
          match certified with
          | .pack _ data _ _ _ =>
              unless data.env.containsHead ``ReifiedPoint do
                throwError "sentence witness lost its datatype environment"
          let fact : Crush.Fact := {
            prop := sentence
            proof := none
            descr := "certified point" }
          let (_, legacy) ← Crush.buildScript {} #[fact]
          unless legacy.factTranslations.isEmpty do
            throwError "default translation unexpectedly enabled datatype certification"
          let (_, certifiedState) ← Crush.buildScript
            { certifyDatatype := true } #[fact]
          unless legacy.commands.map Crush.SMT.commandToString ==
              certifiedState.commands.map Crush.SMT.commandToString do
            throwError "certified point changed the established translation script"
          unless certifiedState.factTranslations.size == 1 do
            throwError "opt-in translation did not retain one translation fact"
          unless certifiedState.datatypeDeclarations.size == 1 do
            throwError "opt-in translation did not retain one certified SMT datatype declaration"
          unless certifiedState.datatypeDeclarationAllocations.size == 1 do
            throwError "certified SMT datatype declaration lost its global allocation link"
          let some declaration := certifiedState.datatypeDeclarations[0]?
            | throwError "certified SMT datatype declaration disappeared"
          let some commandIndex := certifiedState.datatypeDeclarationIndices[0]?
            | throwError "certified SMT datatype declaration lost its state index"
          let some emitted := certifiedState.commands[commandIndex]?
            | throwError "certified SMT datatype declaration index is out of bounds"
          unless Crush.SMT.commandToString emitted ==
              Crush.SMT.commandToString declaration.command do
            throwError "certified SMT datatype declaration drifted after emission"
          let some translation := certifiedState.factTranslations[0]?
            | throwError "retained translation fact disappeared"
          unless translation.expression == sentence do
            throwError "retained translation fact refers to another expression"
          if translation.reifiedSentence.isNone then
            throwError "retained translation fact lost the reified higher-order sentence"
          unless translation.emittedCommands.map Crush.SMT.commandToString ==
              certifiedState.commands.map Crush.SMT.commandToString do
            throwError "retained translation fact lost the emitted command sequence"
          unless translation.datatypeDeclarationIndices.size == translation.datatypes.blocks.size do
            throwError "retained datatype environment is not completely linked"
          unless translation.datatypeDeclarations.size == translation.datatypes.blocks.size do
            throwError "retained datatype environment lost dependency-ordered commands"
          let some linkedIndex := translation.datatypeDeclarationIndices[0]?
            | throwError "retained SMT datatype declaration lost its command index"
          let some linkedCommand := translation.emittedCommands[linkedIndex]?
            | throwError "retained SMT datatype declaration index is outside the emitted command sequence"
          let some retainedCommand := translation.datatypeDeclarations[0]?
            | throwError "retained SMT datatype declaration disappeared"
          unless Crush.SMT.commandToString linkedCommand ==
              Crush.SMT.commandToString retainedCommand do
            throwError "retained SMT datatype declaration does not match the emitted command sequence"
          let (_, repeated) ← Crush.buildScript
            { certifyDatatype := true } #[fact, fact]
          unless repeated.datatypeDeclarations.size == 1 &&
              repeated.factTranslations.size == 2 do
            throwError "repeated facts duplicated an SMT datatype block or lost a fact link"

  let checkTranslatedCommands (label : String) (type : Expr) (declarationCount guardCount : Nat) :
      MetaM Unit := do
    withLocalDeclD `value type fun value => do
      let eqConst ← mkConstWithFreshMVarLevels ``Eq
      let equal := mkApp3 eqConst type value value
      let sentence ← mkForallFVars #[value] equal
      let fact : Crush.Fact := {
        prop := sentence
        proof := none
        descr := label }
      let (_, legacy) ← Crush.buildScript {} #[fact]
      let (_, state) ← Crush.buildScript { certifyDatatype := true } #[fact]
      unless legacy.commands.map Crush.SMT.commandToString ==
          state.commands.map Crush.SMT.commandToString do
        throwError "{label}: certified and legacy translation commands differ"
      unless state.datatypeDeclarations.size == declarationCount do
        throwError "{label}: expected {declarationCount} certified SMT datatype blocks, got \
          {state.datatypeDeclarations.size}"
      unless state.factTranslations.size == 1 do
        throwError "{label}: expected one finalized fact-local datatype translation"
      let some translation := state.factTranslations[0]?
        | throwError "{label}: finalized datatype translation disappeared"
      if translation.reifiedSentence.isNone then
        throwError "{label}: finalized translation lost its reified higher-order sentence"
      unless translation.emittedCommands.size == state.commands.size do
        throwError "{label}: datatype translation retained an intermediate command prefix"
      unless translation.datatypeDeclarations.size == declarationCount do
        throwError "{label}: finalized SMT datatype declaration list has the wrong size"
      unless translation.guardDefinitionCommands.size == guardCount do
        throwError "{label}: finalized guard command list has the wrong size"
      for position in [:declarationCount] do
        let some index := translation.datatypeDeclarationIndices[position]?
          | throwError "{label}: SMT datatype declaration lost its emitted-sequence index"
        let some retained := translation.datatypeDeclarations[position]?
          | throwError "{label}: retained SMT datatype declaration disappeared"
        let some emitted := state.commands[index]?
          | throwError "{label}: SMT datatype declaration index is outside the emitted command sequence"
        unless Crush.SMT.commandToString emitted ==
            Crush.SMT.commandToString retained do
          throwError "{label}: SMT datatype declaration does not match the emitted command sequence"
      for position in [:guardCount] do
        let some index := translation.guardDefinitionIndices[position]?
          | throwError "{label}: guard definition lost its emitted-sequence index"
        let some retained := translation.guardDefinitionCommands[position]?
          | throwError "{label}: retained guard command disappeared"
        let some emitted := state.commands[index]?
          | throwError "{label}: guard definition index is outside the emitted command sequence"
        unless Crush.SMT.commandToString emitted ==
            Crush.SMT.commandToString retained do
          throwError "{label}: guard definition does not match the emitted command sequence"
      let guards := state.commandEncodings.filter fun
        | .datatypeGuard _ => true
        | _ => false
      unless guards.size == guardCount do
        throwError "{label}: expected {guardCount} certified datatype guards, got \
          {guards.size}"
      unless state.commandAllocationLinks.size == state.commandEncodings.size do
        throwError "{label}: an encoded command lost its global allocation link"
      for link in state.commandAllocationLinks do
        let some encoding := state.commandEncodings[link.encodingIndex]?
          | throwError "{label}: encoded-command link index is out of bounds"
        let some emitted := state.commands[link.commandIndex]?
          | throwError "{label}: encoded-command state index is out of bounds"
        unless Crush.SMT.commandToString emitted ==
            Crush.SMT.commandToString encoding.command do
          throwError "{label}: retained command encoding drifted from translation state"
      unless state.datatypeDeclarationIndices.toList.Pairwise (· < ·) do
        throwError "{label}: dependency-ordered datatype command indices were reordered"
  checkTranslatedCommands "Option Int" optionInt 1 1
  checkTranslatedCommands "recursive tree" (mkApp (mkConst ``ReifiedTree) int) 1 1
  checkTranslatedCommands "mutual tree" (mkConst ``ReifiedMutualTree) 1 1
  checkTranslatedCommands "nested option" optionOptionInt 2 2
  checkTranslatedCommands "guarded Nat box" (mkConst ``ReifiedNatBox) 1 1
  checkTranslatedCommands "guarded recursive tree"
    (mkApp (mkConst ``ReifiedTree) (mkConst ``Nat)) 1 1

  let collision := mkConst ``DatatypeNameCollision.Bool
  withLocalDeclD `value collision fun value => do
    let equal := mkApp3 (mkConst ``Eq [1]) collision value value
    let sentence ← mkForallFVars #[value] equal
    let fact : Crush.Fact := {
      prop := sentence
      proof := none
      descr := "datatype name colliding with Bool" }
    let (_, state) ← Crush.buildScript { certifyDatatype := true } #[fact]
    let some declaration := state.datatypeDeclarations[0]?
      | throwError "reserved datatype-name test lost its SMT datatype declaration"
    let first : Fin declaration.block.arity := ⟨0, declaration.wf.blockWF.nonempty⟩
    unless declaration.blockEncoding.name (.sort first) != "Bool" do
      throwError "certified datatype allocator reused the built-in Bool sort"

  withLocalDeclD `leafValue int fun leafValue => do
    let leaf := mkApp2 (mkConst ``ReifiedTree.leaf) int leafValue
    let treeInt := mkApp (mkConst ``ReifiedTree) int
    let eqConst ← mkConstWithFreshMVarLevels ``Eq
    let equal := mkApp3 eqConst treeInt leaf leaf
    let sentence ← mkForallFVars #[leafValue] equal
    let some (.pack _ data _ _ _) ← reifySentence? sentence
      | throwError "recursive constructor sentence was not certified"
    unless data.env.containsHead ``ReifiedTree do
      throwError "recursive constructor sentence lost its datatype block"

  withLocalDeclD `box (mkConst ``ReifiedFnBox) fun box => do
    let eqConst ← mkConstWithFreshMVarLevels ``Eq
    let equal := mkApp3 eqConst (mkConst ``ReifiedFnBox) box box
    let sentence ← mkForallFVars #[box] equal
    let fact : Crush.Fact := {
      prop := sentence
      proof := none
      descr := "unsupported function field" }
    let (_, state) ← Crush.buildScript { certifyDatatype := true } #[fact]
    unless state.trustReasons.any fun
        | .datatype (.functionField ``ReifiedFnBox.mk 0) => true
        | _ => false do
      throwError "translation fallback lost the function-field rejection reason"

  let someConst ← mkConstWithFreshMVarLevels ``Option.some
  let partialSome := mkApp someConst int
  let partialType ← inferType partialSome
  let eqConst ← mkConstWithFreshMVarLevels ``Eq
  let partialEq := mkApp3 eqConst partialType partialSome partialSome
  if (← reifySentence? partialEq).isSome then
    throwError "datatype-aware sentence reification accepted a partial constructor"

end Crush.Metatheory.Reification.Tests
