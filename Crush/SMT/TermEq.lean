import Crush.SMT.Syntax

/-!
# Decidable equality for recursive SMT terms

`Term` and `Attr` recurse through arrays, so Lean's standard equality deriver
cannot construct their instances directly.  The explicit list recursion below
is used at proof-carrying translator boundaries that must compare retained raw
commands without trusting rendered strings or hashes.
-/

namespace Crush.SMT

instance : DecidableEq Literal := fun left right => by
  cases left <;> cases right <;> simp <;> exact inferInstance

namespace Term

mutual
  private def decEq : (left right : Term) → Decidable (left = right)
    | .lit left, .lit right =>
        if equal : left = right then isTrue (by cases equal; rfl)
        else isFalse fun assumed => by cases assumed; exact equal rfl
    | .bvar left, .bvar right =>
        if equal : left = right then isTrue (by cases equal; rfl)
        else isFalse fun assumed => by cases assumed; exact equal rfl
    | .app leftName leftArgs, .app rightName rightArgs =>
        if namesEq : leftName = rightName then
          match listDecEq leftArgs.toList rightArgs.toList with
          | isFalse different => isFalse fun equal => by
              injection equal with _ argsEq
              exact different (congrArg Array.toList argsEq)
          | isTrue argsEq => isTrue (by
              cases namesEq
              have arraysEq := Array.toList_inj.mp argsEq
              cases arraysEq
              rfl)
        else isFalse fun equal => by
          injection equal with equalNames
          exact namesEq equalNames
    | .letE leftBindings leftBody, .letE rightBindings rightBody =>
        match bindingDecEq leftBindings.toList rightBindings.toList with
        | isFalse different => isFalse fun equal => by
            injection equal with bindingsEq
            exact different (congrArg Array.toList bindingsEq)
        | isTrue bindingsEq =>
          match decEq leftBody rightBody with
          | isFalse different => isFalse fun equal => by
              injection equal with _ bodyEq
              exact different bodyEq
          | isTrue bodyEq => isTrue (by
              have arraysEq := Array.toList_inj.mp bindingsEq
              cases arraysEq
              cases bodyEq
              rfl)
    | .forallE leftBinders leftBody, .forallE rightBinders rightBody
    | .existsE leftBinders leftBody, .existsE rightBinders rightBody
    | .lam leftBinders leftBody, .lam rightBinders rightBody =>
        if bindersEq : leftBinders = rightBinders then
          match decEq leftBody rightBody with
          | isFalse different => isFalse fun equal => by
              injection equal with _ bodyEq
              exact different bodyEq
          | isTrue bodyEq => isTrue (by
              cases bindersEq
              cases bodyEq
              rfl)
        else isFalse fun equal => by
          injection equal with equalBinders
          exact bindersEq equalBinders
    | .annot leftBody leftAttrs, .annot rightBody rightAttrs =>
        match decEq leftBody rightBody with
        | isFalse different => isFalse fun equal => by
            injection equal with bodyEq
            exact different bodyEq
        | isTrue bodyEq =>
          match attrListDecEq leftAttrs.toList rightAttrs.toList with
          | isFalse different => isFalse fun equal => by
              injection equal with _ attrsEq
              exact different (congrArg Array.toList attrsEq)
          | isTrue attrsEq => isTrue (by
              cases bodyEq
              have arraysEq := Array.toList_inj.mp attrsEq
              cases arraysEq
              rfl)
    | .lit _, .bvar _ | .lit _, .app _ _ | .lit _, .letE _ _
    | .lit _, .forallE _ _ | .lit _, .existsE _ _ | .lit _, .lam _ _
    | .lit _, .annot _ _ | .bvar _, .lit _ | .bvar _, .app _ _
    | .bvar _, .letE _ _ | .bvar _, .forallE _ _ | .bvar _, .existsE _ _
    | .bvar _, .lam _ _ | .bvar _, .annot _ _ | .app _ _, .lit _
    | .app _ _, .bvar _ | .app _ _, .letE _ _ | .app _ _, .forallE _ _
    | .app _ _, .existsE _ _ | .app _ _, .lam _ _ | .app _ _, .annot _ _
    | .letE _ _, .lit _ | .letE _ _, .bvar _ | .letE _ _, .app _ _
    | .letE _ _, .forallE _ _ | .letE _ _, .existsE _ _
    | .letE _ _, .lam _ _ | .letE _ _, .annot _ _ | .forallE _ _, .lit _
    | .forallE _ _, .bvar _ | .forallE _ _, .app _ _
    | .forallE _ _, .letE _ _ | .forallE _ _, .existsE _ _
    | .forallE _ _, .lam _ _ | .forallE _ _, .annot _ _
    | .existsE _ _, .lit _ | .existsE _ _, .bvar _
    | .existsE _ _, .app _ _ | .existsE _ _, .letE _ _
    | .existsE _ _, .forallE _ _ | .existsE _ _, .lam _ _
    | .existsE _ _, .annot _ _ | .lam _ _, .lit _ | .lam _ _, .bvar _
    | .lam _ _, .app _ _ | .lam _ _, .letE _ _ | .lam _ _, .forallE _ _
    | .lam _ _, .existsE _ _ | .lam _ _, .annot _ _ | .annot _ _, .lit _
    | .annot _ _, .bvar _ | .annot _ _, .app _ _ | .annot _ _, .letE _ _
    | .annot _ _, .forallE _ _ | .annot _ _, .existsE _ _
    | .annot _ _, .lam _ _ => isFalse nofun
  termination_by left right => structuralSize left + structuralSize right
  decreasing_by all_goals
    simp [structuralSize] <;> omega

  private def attrDecEq : (left right : Attr) → Decidable (left = right)
    | .named left, .named right =>
        if equal : left = right then isTrue (by cases equal; rfl)
        else isFalse fun assumed => by cases assumed; exact equal rfl
    | .pattern left, .pattern right =>
        match listDecEq left.toList right.toList with
        | isFalse different => isFalse fun equal => by
            injection equal with termsEq
            exact different (congrArg Array.toList termsEq)
        | isTrue termsEq => isTrue (by
            have arraysEq := Array.toList_inj.mp termsEq
            cases arraysEq
            rfl)
    | .keyword leftName leftValue, .keyword rightName rightValue =>
        if nameEq : leftName = rightName then
          if valueEq : leftValue = rightValue then
            isTrue (by cases nameEq; cases valueEq; rfl)
          else isFalse fun equal => by
            injection equal with _ equalValue
            exact valueEq equalValue
        else isFalse fun equal => by
          injection equal with equalName
          exact nameEq equalName
    | .named _, .pattern _ | .named _, .keyword _ _
    | .pattern _, .named _ | .pattern _, .keyword _ _
    | .keyword _ _, .named _ | .keyword _ _, .pattern _ => isFalse nofun
  termination_by left right => attrStructuralSize left + attrStructuralSize right
  decreasing_by all_goals
    simp [attrStructuralSize] <;> omega

  private def listDecEq : (left right : List Term) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse nofun
    | left :: lefts, right :: rights =>
        match decEq left right with
        | isFalse different => isFalse fun equal => by
            injection equal with headEq
            exact different headEq
        | isTrue headEq =>
          match listDecEq lefts rights with
          | isFalse different => isFalse fun equal => by
              injection equal with _ tailEq
              exact different tailEq
          | isTrue tailEq => isTrue (by
              cases headEq
              cases tailEq
              rfl)
  termination_by left right => listStructuralSize left + listStructuralSize right
  decreasing_by all_goals
    simp [listStructuralSize] <;> omega

  private def attrListDecEq :
      (left right : List Attr) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse nofun
    | left :: lefts, right :: rights =>
        match attrDecEq left right with
        | isFalse different => isFalse fun equal => by
            injection equal with headEq
            exact different headEq
        | isTrue headEq =>
          match attrListDecEq lefts rights with
          | isFalse different => isFalse fun equal => by
              injection equal with _ tailEq
              exact different tailEq
          | isTrue tailEq => isTrue (by
              cases headEq
              cases tailEq
              rfl)
  termination_by left right =>
    attrListStructuralSize left + attrListStructuralSize right
  decreasing_by all_goals
    simp [attrListStructuralSize] <;> omega

  private def bindingDecEq :
      (left right : List (String × Term)) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse nofun
    | (leftName, left) :: lefts, (rightName, right) :: rights =>
        if nameEq : leftName = rightName then
          match decEq left right with
          | isFalse different => isFalse fun equal => by
              injection equal with headEq
              exact different (congrArg Prod.snd headEq)
          | isTrue headEq =>
            match bindingDecEq lefts rights with
            | isFalse different => isFalse fun equal => by
                injection equal with _ tailEq
                exact different tailEq
            | isTrue tailEq => isTrue (by
                cases nameEq
                cases headEq
                cases tailEq
                rfl)
        else isFalse fun equal => by
          injection equal with headEq
          exact nameEq (congrArg Prod.fst headEq)
  termination_by left right =>
    bindingListStructuralSize left + bindingListStructuralSize right
  decreasing_by all_goals
    simp [bindingListStructuralSize] <;> omega
end

end Term

instance : DecidableEq Term := Term.decEq
instance : DecidableEq Attr := Term.attrDecEq

instance : DecidableEq FunDef := fun left right => by
  cases left with
  | mk leftName leftArgs leftResult leftBody =>
    cases right with
    | mk rightName rightArgs rightResult rightBody =>
      exact decidable_of_iff
        (leftName = rightName ∧ leftArgs = rightArgs ∧
          leftResult = rightResult ∧ leftBody = rightBody) (by
            constructor
            · rintro ⟨rfl, rfl, rfl, rfl⟩
              rfl
            · intro equal
              injection equal with nameEq argsEq resultEq bodyEq
              exact ⟨nameEq, argsEq, resultEq, bodyEq⟩)

/- Exact command equality becomes decidable once recursive terms, attributes,
and function definitions have their explicit instances. Translator agreement
uses this instance to turn a successful whole-array comparison into an equality
proof rather than comparing rendered strings or hashes. A regular comment is
intentional: Lean documentation comments cannot attach to `deriving instance`. -/
deriving instance DecidableEq for Command

end Crush.SMT
