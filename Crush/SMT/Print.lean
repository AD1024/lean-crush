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

/-- A symbol is "simple" if it needs no `|…|` quoting in SMT-LIB. -/
def isSimpleSymbol (s : String) : Bool :=
  let specials := "~!@$%^&*_-+=<>.?/"
  !s.isEmpty
    && (s.front.isAlpha || specials.contains s.front)
    && s.toList.all (fun c => c.isAlphanum || specials.contains c)

def quoteSymbol (s : String) : String :=
  if isSimpleSymbol s then s else "|" ++ s ++ "|"

def identToString : Ident → String
  | .symb s => quoteSymbol s
  | .indexed s idx =>
    let parts := idx.toList.map (fun x => match x with | .inl y => y | .inr n => toString n)
    "(_ " ++ quoteSymbol s ++ " " ++ String.intercalate " " parts ++ ")"

instance : ToString Ident := ⟨identToString⟩

partial def sortToString (binders : List String) : SSort → String
  | .bvar i => binders[i]?.getD s!"?bv{i}"
  | .app f #[] => identToString f
  | .app f args =>
    "(" ++ identToString f ++ " " ++
      String.intercalate " " (args.toList.map (sortToString binders)) ++ ")"

instance : ToString SSort := ⟨sortToString []⟩

/-- Render a bitvector literal via the unambiguous decimal indexed form. -/
def bvLiteral (width value : Nat) : String := s!"(_ bv{value} {width})"

def literalToString : Literal → String
  | .str s      => "\"" ++ s.replace "\"" "\"\"" ++ "\""
  | .num n      => toString n
  | .bitvec w v => bvLiteral w v
  | .bool b     => if b then "true" else "false"

instance : ToString Literal := ⟨literalToString⟩

mutual
  partial def termToString (binders : List String) : Term → String
    | .lit l => literalToString l
    | .bvar i => binders[i]?.getD s!"?bv{i}"
    | .app f #[] => identToString f
    | .app f args =>
      "(" ++ identToString f ++ " " ++
        String.intercalate " " (args.toList.map (termToString binders)) ++ ")"
    | .letE binds body =>
      let names := binds.toList.map (·.1)
      let bindStr := binds.toList.map (fun (n, t) => s!"({quoteSymbol n} {termToString binders t})")
      let inner := termToString (names.reverse ++ binders) body
      "(let (" ++ String.intercalate " " bindStr ++ ") " ++ inner ++ ")"
    | .forallE bs body => quantToString "forall" binders bs body
    | .existsE bs body => quantToString "exists" binders bs body
    | .annot t attrs =>
      "(! " ++ termToString binders t ++ " " ++
        String.intercalate " " (attrs.toList.map (attrToString binders)) ++ ")"

  partial def quantToString (kw : String) (binders : List String)
      (bs : Array (String × SSort)) (body : Term) : String :=
    let names := bs.toList.map (·.1)
    let sortedVars := bs.toList.map (fun (n, s) => s!"({quoteSymbol n} {sortToString binders s})")
    let inner := termToString (names.reverse ++ binders) body
    s!"({kw} (" ++ String.intercalate " " sortedVars ++ ") " ++ inner ++ ")"

  partial def attrToString (binders : List String) : Attr → String
    | .named n => s!":named {quoteSymbol n}"
    | .pattern ts => ":pattern (" ++ String.intercalate " " (ts.toList.map (termToString binders)) ++ ")"
    | .keyword k none => s!":{k}"
    | .keyword k (some v) => s!":{k} {v}"
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
  | .echo s => s!"(echo \"{s}\")"
  | .exit => "(exit)"

instance : ToString Command := ⟨commandToString⟩

/-- Render a full script. -/
def scriptToString (cmds : Array Command) : String :=
  String.intercalate "\n" (cmds.toList.map toString)

end Crush.SMT
