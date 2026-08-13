import Crush.SMT.Syntax

/-!
# Printing the SMT IR to SMT-LIB 2.6 text

Rendering is separated from the IR so that alternative concrete syntaxes
(e.g. a TPTP THF backend) can reuse the same abstract commands. De Bruijn
`bvar`s are resolved against a binder stack passed down explicitly.

Function names here avoid the `.toString` field name so they don't shadow the
`ToString` instances used for interpolation.
-/

namespace Crush.SMT

/-- Characters accepted by both the SMT printer and the `(smt| …)` parser.

`$` is legal in SMT-LIB but reserved for quotation splices in Lean, so crush
quotes it instead of maintaining two subtly different symbol alphabets. -/
def simpleSymbolSpecials : String := "~!@%^&*_-+=<>.?/"

def isInitialSimpleSymbolChar (c : Char) : Bool :=
  c.isAlpha || simpleSymbolSpecials.contains c

def isSimpleSymbolChar (c : Char) : Bool :=
  c.isAlphanum || simpleSymbolSpecials.contains c

/-- SMT-LIB reserved words cannot be emitted as unquoted symbols. -/
def isReservedSymbol (s : String) : Bool :=
  s == "_" || s == "!" || s == "as" || s == "BINARY" ||
    s == "DECIMAL" || s == "exists" || s == "HEXADECIMAL" ||
    s == "forall" || s == "let" || s == "match" || s == "NUMERAL" ||
    s == "par" || s == "STRING"

/-- A symbol is "simple" if it needs no `|…|` quoting in SMT-LIB. -/
def isSimpleSymbol (s : String) : Bool :=
  !s.isEmpty
    && !isReservedSymbol s
    && isInitialSimpleSymbolChar s.front
    && s.toList.all isSimpleSymbolChar

private def encodedSymbolPrefix := "crush_encoded_"

/-- Injectively encode a symbol that cannot occur inside SMT-LIB `|…|` quoting.

The prefix is reserved by encoding source names that already begin with it, so
an encoded name cannot collide with an ordinary user symbol. -/
private def encodeSymbol (s : String) : String :=
  encodedSymbolPrefix ++ String.intercalate "_"
    (s.toList.map fun c => String.ofList (Nat.toDigits 16 c.toNat))

def quoteSymbol (s : String) : String :=
  if s.startsWith encodedSymbolPrefix ||
      s.toList.any (fun c => c == '|' || c == '\\' || c.toNat < 0x20 || c.toNat > 0x7E) then
    encodeSymbol s
  else if isSimpleSymbol s then
    s
  else
    "|" ++ s ++ "|"

def identToString : Ident → String
  | .symb s => quoteSymbol s
  | .indexed s idx =>
    let parts := idx.toList.map (fun x => match x with | .inl y => y | .inr n => toString n)
    "(_ " ++ quoteSymbol s ++ " " ++ String.intercalate " " parts ++ ")"

instance : ToString Ident := ⟨identToString⟩

-- `SSort` is a *nested* inductive (`app` carries `Array SSort`), and recursing
-- through `Array.map` hides the recursive call from the termination checker.
-- Recursing through an explicit mutual list helper exposes the structural descent,
-- so these are total definitions rather than `partial` — which matters because a
-- `partial` def is opaque to `decide`/`simp`/`rfl` and so cannot be reasoned about.
mutual
  /-- Render a sort to SMT-LIB text. -/
  def sortToString (binders : List String) : SSort → String
    | .bvar i => binders[i]?.getD s!"?bv{i}"
    | .app f args =>
      if args.isEmpty then identToString f
      else
        "(" ++ identToString f ++ " " ++
          String.intercalate " " (sortListToStrings binders args.toList) ++ ")"

  /-- Render each sort in a list; the helper that makes the descent structural. -/
  def sortListToStrings (binders : List String) : List SSort → List String
    | [] => []
    | s :: ss => sortToString binders s :: sortListToStrings binders ss
end

instance : ToString SSort := ⟨sortToString []⟩

/-- Render a bitvector literal via the unambiguous decimal indexed form. -/
def bvLiteral (width value : Nat) : String := s!"(_ bv{value} {width})"

/-- Render a Lean string as an SMT-LIB 2.6 string literal.

SMT-LIB string literals are enclosed in `"`, escape an embedded quote by doubling
it, and are otherwise sequences of printable ASCII; any other character must be
written with the `\u{…}` escape. A literal backslash must itself be emitted as
`\u{5c}`: otherwise a Lean substring such as `\u{61}` is reinterpreted by the SMT
parser as the character `a`.

`str.len` counts codepoints, matching Lean's `String.length`, so a codepoint-wise
escape keeps lengths in agreement. `checkScript` rejects codepoints above SMT-LIB
2.6's five-hex-digit escape range before this printer is called by `crush`. -/
def escapeSmtString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == '"' then acc ++ "\"\""
    else if c == '\\' then acc ++ "\\u{5c}"
    else if c.toNat ≥ 0x20 && c.toNat ≤ 0x7E then acc.push c
    else acc ++ s!"\\u\{{String.ofList (Nat.toDigits 16 c.toNat)}}"

def literalToString : Literal → String
  | .str s      => "\"" ++ escapeSmtString s ++ "\""
  | .num n      => toString n
  | .bitvec w v => bvLiteral w v
  | .bool b     => if b then "true" else "false"

instance : ToString Literal := ⟨literalToString⟩

-- `Term` and `Attr` are mutually nested inductives, each carrying `Array` of the
-- other. As with sorts above, the recursion goes through explicit list helpers so
-- the structural descent is visible and these are total rather than `partial`.
-- Note the `letE`/`quantToString` cases need their *own* helpers rather than reusing
-- `termListToStrings`: an intervening `.map (·.2)` to project the pair would itself
-- defeat the termination checker.
mutual
  /-- Render a term to SMT-LIB text, resolving `bvar`s against `binders`. -/
  def termToString (binders : List String) : Term → String
    | .lit l => literalToString l
    | .bvar i => binders[i]?.getD s!"?bv{i}"
    -- A nullary application renders as the bare symbol. Written as an `if` on the
    -- argument list rather than an `#[]` pattern: the latter compiles to a decidable
    -- equality test on the array, which blocks Lean from deriving the unfold
    -- equations a well-founded definition needs.
    | .app f args =>
      if args.isEmpty then identToString f
      else
        "(" ++ identToString f ++ " " ++
          String.intercalate " " (termListToStrings binders args.toList) ++ ")"
    | .letE binds body =>
      let names := binds.toList.map (·.1)
      let bindStr := letBindsToStrings binders binds.toList
      let inner := termToString (names.reverse ++ binders) body
      "(let (" ++ String.intercalate " " bindStr ++ ") " ++ inner ++ ")"
    | .forallE bs body => quantToString "forall" binders bs body
    | .existsE bs body => quantToString "exists" binders bs body
    | .lam bs body => quantToString "lambda" binders bs body
    | .annot t attrs =>
      "(! " ++ termToString binders t ++ " " ++
        String.intercalate " " (attrListToStrings binders attrs.toList) ++ ")"
  termination_by t => sizeOf t
  decreasing_by
    -- Each recursive call descends into a strict sub-term. The `Array → List`
    -- conversions are the only non-obvious step: `sizeOf a.toList < sizeOf a` holds
    -- because `sizeOf ⟨l⟩ = 1 + sizeOf l` (`Array.mk.sizeOf_spec`), so destructing
    -- the array exposes the inequality to `omega`.
    all_goals first
      | omega
      | (obtain ⟨l⟩ := ts; simp [Array.mk.sizeOf_spec]; omega)
      | (obtain ⟨l⟩ := args; simp [Array.mk.sizeOf_spec]; omega)
      | (obtain ⟨l⟩ := attrs; simp [Array.mk.sizeOf_spec]; omega)
      | (obtain ⟨l⟩ := binds; simp [Array.mk.sizeOf_spec]; omega)
      | simp_wf

  /-- Render `(forall|exists|lambda) ((x σ) …) body`. -/
  def quantToString (kw : String) (binders : List String)
      (bs : Array (String × SSort)) (body : Term) : String :=
    let names := bs.toList.map (·.1)
    let sortedVars := binderListToStrings binders bs.toList
    let inner := termToString (names.reverse ++ binders) body
    s!"({kw} (" ++ String.intercalate " " sortedVars ++ ") " ++ inner ++ ")"
  termination_by sizeOf bs + sizeOf body
  decreasing_by
    -- `0 < sizeOf bs`: an array's `sizeOf` is `1 + sizeOf toList`, hence positive.
    obtain ⟨l⟩ := bs; simp [Array.mk.sizeOf_spec]; omega

  def attrToString (binders : List String) : Attr → String
    | .named n => s!":named {quoteSymbol n}"
    | .pattern ts =>
      ":pattern (" ++ String.intercalate " " (termListToStrings binders ts.toList) ++ ")"
    | .keyword k none => s!":{k}"
    | .keyword k (some v) => s!":{k} {v}"
  termination_by a => sizeOf a
  decreasing_by
    obtain ⟨l⟩ := ts; simp [Array.mk.sizeOf_spec]; omega

  def termListToStrings (binders : List String) : List Term → List String
    | [] => []
    | t :: ts => termToString binders t :: termListToStrings binders ts
  termination_by ts => sizeOf ts
  decreasing_by all_goals (simp_wf; omega)

  def attrListToStrings (binders : List String) : List Attr → List String
    | [] => []
    | a :: as => attrToString binders a :: attrListToStrings binders as
  termination_by as => sizeOf as
  decreasing_by all_goals (simp_wf; omega)

  def letBindsToStrings (binders : List String) : List (String × Term) → List String
    | [] => []
    | (n, t) :: rest =>
      s!"({quoteSymbol n} {termToString binders t})" :: letBindsToStrings binders rest
  termination_by bs => sizeOf bs
  decreasing_by all_goals (simp_wf; omega)

  def binderListToStrings (binders : List String) : List (String × SSort) → List String
    | [] => []
    | (n, s) :: rest =>
      s!"({quoteSymbol n} {sortToString binders s})" :: binderListToStrings binders rest
end

instance : ToString Term := ⟨termToString []⟩

def ctorDeclToString (params : List String) : CtorDecl → String
  | ⟨name, sels⟩ =>
    let selStr := sels.toList.map (fun (n, s) => s!"({quoteSymbol n} {sortToString params s})")
    "(" ++ String.intercalate " " (quoteSymbol name :: selStr) ++ ")"

def datatypeDeclToString : DatatypeDecl → String
  | ⟨params, ctors⟩ =>
    let body := "(" ++ String.intercalate " " (ctors.toList.map (ctorDeclToString params.toList)) ++ ")"
    if params.isEmpty then body
    else "(par (" ++ String.intercalate " " params.toList ++ ") " ++ body ++ ")"

def commandToString : Command → String
  | .setLogic l => s!"(set-logic {l})"
  | .setOption k v => s!"(set-option :{k} {v})"
  | .declSort n arity => s!"(declare-sort {quoteSymbol n} {arity})"
  | .defSort n params body =>
    s!"(define-sort {quoteSymbol n} (" ++ String.intercalate " " params.toList ++ ") " ++
      sortToString params.toList body ++ ")"
  | .declFun n args res =>
    s!"(declare-fun {quoteSymbol n} (" ++ String.intercalate " " (args.toList.map toString) ++
      s!") {res})"
  | .defFun rec_ n args res body =>
    let kw := if rec_ then "define-fun-rec" else "define-fun"
    let argStr := args.toList.map (fun (nm, s) => s!"({quoteSymbol nm} {s})")
    let names := args.toList.map (·.1)
    s!"({kw} {quoteSymbol n} (" ++ String.intercalate " " argStr ++ s!") {res} " ++
      termToString names.reverse body ++ ")"
  | .defFunsRec defs =>
    let signatures := defs.toList.map fun d =>
      let args := d.args.toList.map fun (nm, s) => s!"({quoteSymbol nm} {s})"
      s!"({quoteSymbol d.name} (" ++ String.intercalate " " args ++ s!") {d.resSort})"
    let bodies := defs.toList.map fun d =>
      termToString (d.args.toList.map (·.1)).reverse d.body
    "(define-funs-rec (" ++ String.intercalate " " signatures ++ ") (" ++
      String.intercalate " " bodies ++ "))"
  | .declDatatypes infos =>
    let decls := infos.toList.map (fun (n, ar, _) => s!"({quoteSymbol n} {ar})")
    let bodies := infos.toList.map (fun (_, _, d) => datatypeDeclToString d)
    "(declare-datatypes (" ++ String.intercalate " " decls ++ ") (" ++
      String.intercalate " " bodies ++ "))"
  | .assert t => s!"(assert {t})"
  | .checkSat => "(check-sat)"
  | .getModel => "(get-model)"
  | .getProof => "(get-proof)"
  | .getUnsatCore => "(get-unsat-core)"
  | .echo s => "(echo \"" ++ escapeSmtString s ++ "\")"
  | .exit => "(exit)"

instance : ToString Command := ⟨commandToString⟩

/-- Render a full script. -/
def scriptToString (cmds : Array Command) : String :=
  String.intercalate "\n" (cmds.toList.map toString)

end Crush.SMT
