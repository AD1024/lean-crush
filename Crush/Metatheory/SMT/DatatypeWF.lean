import Crush.Metatheory.SMT.Datatype
import Crush.Metatheory.SMT.Semantics
import Crush.Metatheory.Datatype.Semantics

/-! Syntactic well-formedness of native datatype declarations. -/

namespace Crush.Metatheory.SMT.Datatype

open Crush.Metatheory.Datatype

/-- Syntactic freshness retained by the allocator for one exact native block. -/
structure CommandWF {arity : Nat} (block : Block arity)
    (encoding : BlockEncoding arity) : Prop where
  blockWF : block.WF
  /-- The exact raw declaration passes the structural check used by the
  modeled script validator and `Command.InFragment`. -/
  structureCheck : Crush.SMT.datatypesStructurallyWellFormed
    (entries block encoding) = true
  /-- The exact raw declaration passes the same finite-constructor check used
  by the modeled SMT script validator. Keeping this evidence on the canonical
  command certificate prevents the raw and typed admission paths from
  drifting apart. -/
  finiteValueCheck : Crush.SMT.datatypesProductive (entries block encoding) = true
  names : encoding.WF
  sorts_fresh : ∀ data : DataRef block,
    dataSort encoding data ≠ Crush.SMT.boolSort ∧
    dataSort encoding data ≠ Crush.SMT.intSort ∧
    dataSort encoding data ≠ Crush.SMT.stringSort
  symbols : (Crush.SMT.datatypeSymbols (entries block encoding)).Nodup
  symbols_fresh : ∀ symbol ∈
    Crush.SMT.datatypeSymbols (entries block encoding),
      Crush.SMT.NotBuiltin symbol

/-- Native datatype sorts retain their intrinsic mutual-block indices. -/
theorem dataSort_injective {arity : Nat} {encoding : BlockEncoding arity}
    (wf : encoding.WF) : Function.Injective (dataSort encoding) := by
  intro left right equal
  unfold dataSort at equal
  injection equal with identEq
  injection identEq with nameEq
  exact wf nameEq

/-- A concrete list of mutual-block sort names discharges the only local
injectivity condition required by the datatype carrier proof. -/
theorem BlockEncoding.wf_of_names {arity : Nat} (encoding : BlockEncoding arity)
    (nodup : (List.ofFn fun data : Fin arity =>
      encoding.name (.sort data)).Nodup) : encoding.WF := by
  intro left right equal
  have leftLt : left.val < (List.ofFn fun data : Fin arity =>
      encoding.name (.sort data)).length := by simp
  have rightLt : right.val < (List.ofFn fun data : Fin arity =>
      encoding.name (.sort data)).length := by simp
  apply Fin.ext
  apply (List.getElem_inj (h₀ := leftLt) (h₁ := rightLt) nodup).mp
  simpa using equal

/-- Every typed constructor reference occurs in the raw command. -/
theorem raw_ctor_mem {arity : Nat} {block : Block arity}
    (encoding : BlockEncoding arity) {data : DataRef block}
    {ctor : CtorDecl arity} (ref : CtorRef block data ctor) :
    (dataSort encoding data,
      ctorDecl (block := block) encoding data ref.index ctor) ∈
      Crush.SMT.datatypeCtors (entries block encoding) := by
  simp only [Crush.SMT.datatypeCtors, entries, List.mem_flatMap, List.mem_map]
  refine ⟨(encoding.name (.sort data), 0,
    dataDecl (block := block) encoding data), ?_, ?_⟩
  · exact ⟨data, by simp, rfl⟩
  · refine ⟨ctorDecl (block := block) encoding data ref.index ctor, ?_, rfl⟩
    change ctorDecl (block := block) encoding data ref.index ctor ∈
      (block.decl data).ctors.mapIdx fun index ctor =>
        ctorDecl (block := block) encoding data index ctor
    rw [List.mem_mapIdx]
    exact ⟨ref.index, ref.index_lt, by congr 1; exact ref.getElem_index⟩

private theorem mapIdx_snd {α β γ : Type} (values : List α)
    (name : Nat → α → β) (image : α → γ) :
    (values.mapIdx fun index value =>
      (name index value, image value)).map Prod.snd = values.map image := by
  induction values generalizing name with
  | nil => rfl
  | cons value values ih => simp [List.mapIdx_cons, ih]

@[simp] theorem raw_ctor_argSorts {arity : Nat} {block : Block arity}
    (encoding : BlockEncoding arity) (data : DataRef block) (index : Nat)
    (ctor : CtorDecl arity) :
    (ctorDecl (block := block) encoding data index ctor).argSorts =
      ctor.fields.map fun field =>
        fieldSort (block := block) encoding field.sort := by
  simp [Crush.SMT.CtorDecl.argSorts, ctorDecl, mapIdx_snd]

/-- Every raw constructor comes from one typed reference. -/
theorem raw_ctor_ref {arity : Nat} {block : Block arity}
    (encoding : BlockEncoding arity) {sort : Crush.SMT.SSort}
    {rawCtor : Crush.SMT.CtorDecl}
    (member : (sort, rawCtor) ∈
      Crush.SMT.datatypeCtors (entries block encoding)) :
    ∃ data : DataRef block, ∃ ctor : CtorDecl arity,
      ∃ ref : CtorRef block data ctor,
        sort = dataSort encoding data ∧
        rawCtor = ctorDecl (block := block) encoding data ref.index ctor := by
  simp only [Crush.SMT.datatypeCtors, entries, List.mem_flatMap,
    List.mem_map] at member
  rcases member with ⟨⟨name, count, decl⟩, entryMem,
    ctor, ctorMem, equal⟩
  rcases entryMem with ⟨data, dataMem, entryEq⟩
  cases entryEq
  change ctor ∈ (block.decl data).ctors.mapIdx fun index ctor =>
    ctorDecl (block := block) encoding data index ctor at ctorMem
  rw [List.mem_mapIdx] at ctorMem
  rcases ctorMem with ⟨index, inBounds, ctorEq⟩
  let ref : CtorRef block data (block.decl data).ctors[index] :=
    Ref.ofIdx (block.decl data).ctors index inBounds
  refine ⟨data, (block.decl data).ctors[index], ref, ?_, ?_⟩
  · exact congrArg Prod.fst equal.symm
  · have rawEq := congrArg Prod.snd equal.symm
    change rawCtor = ctor at rawEq
    calc
      rawCtor = ctor := rawEq
      _ = ctorDecl (block := block) encoding data index
          (block.decl data).ctors[index] := ctorEq.symm
      _ = ctorDecl (block := block) encoding data ref.index
          (block.decl data).ctors[index] := by
        congr 1
        exact (Ref.index_ofIdx (block.decl data).ctors index inBounds).symm

/-- Every raw datatype entry comes from one typed datatype reference. -/
theorem raw_entry_ref {arity : Nat} (block : Block arity)
    (encoding : BlockEncoding arity) {name : String} {count : Nat}
    {decl : Crush.SMT.DatatypeDecl}
    (member : (name, count, decl) ∈ (entries block encoding).toList) :
    ∃ data : DataRef block,
      name = encoding.name (.sort data) ∧ count = 0 ∧
        decl = dataDecl (block := block) encoding data := by
  simp only [entries] at member
  rcases List.mem_map.mp member with ⟨data, dataMem, equal⟩
  cases equal
  exact ⟨data, rfl, rfl, rfl⟩

/-- Every sort in one raw block comes from one typed datatype reference. -/
theorem raw_sort_ref {arity : Nat} (block : Block arity)
    (encoding : BlockEncoding arity) {sort : Crush.SMT.SSort}
    (member : sort ∈ Crush.SMT.datatypeSorts (entries block encoding)) :
    ∃ data : DataRef block, sort = dataSort encoding data := by
  simp only [Crush.SMT.datatypeSorts, entries, List.mem_map] at member
  rcases member with ⟨⟨name, count, decl⟩, entryMem, sortEq⟩
  rcases entryMem with ⟨data, dataMem, entryEq⟩
  cases entryEq
  exact ⟨data, sortEq.symm⟩

/-- Structural, name-freshness, and finite-constructor evidence discharges the
raw command's datatype well-formedness predicate. -/
theorem wellFormed {arity : Nat} {block : Block arity}
    {encoding : BlockEncoding arity} (wf : CommandWF block encoding) :
    Crush.SMT.DatatypesWellFormed (entries block encoding) := by
  exact ⟨wf.structureCheck, wf.finiteValueCheck⟩

end Crush.Metatheory.SMT.Datatype
