import CoreChecker.Model

namespace CoreChecker

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\''

partial def stripBlockComments (s : String) : String :=
  let rec go (cs : List Char) (depth : Nat) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | '/' :: '-' :: rest => go rest (depth + 1) acc
    | '-' :: '/' :: rest => go rest (depth - 1) acc
    | c :: rest =>
        if depth == 0 then go rest depth (c :: acc) else go rest depth acc
  String.mk (go s.data 0 [])

def stripLineComment (s : String) : String :=
  match s.splitOn "--" with
  | [] => s
  | h :: _ => h

def tokenize (s : String) : Array String := Id.run do
  let cs := s.data.toArray
  let mut out := #[]
  let mut i := 0
  while h : i < cs.size do
    let c := cs[i]
    if c.isWhitespace then
      i := i + 1
    else if c == ':' && i + 1 < cs.size && cs[i+1]! == '=' then
      out := out.push ":="
      i := i + 2
    else if c == '-' && i + 1 < cs.size && cs[i+1]! == '>' then
      out := out.push "->"
      i := i + 2
    else if c == '(' || c == ')' || c == ':' then
      out := out.push (String.singleton c)
      i := i + 1
    else if c == '→' then
      out := out.push "->"
      i := i + 1
    else if c == '×' then
      out := out.push "prod"
      i := i + 1
    else if c == '∘' then
      out := out.push "o"
      i := i + 1
    else if c == '#' || c == '@' then
      let start := i
      let mut j := i + 1
      while j < cs.size && isIdentChar cs[j]! do
        j := j + 1
      out := out.push (String.mk ((cs.extract start j).toList))
      i := j
    else
      let start := i
      let mut j := i
      while j < cs.size && isIdentChar cs[j]! do
        j := j + 1
      if start == j then
        out := out.push (String.singleton c)
        i := i + 1
      else
        out := out.push (String.mk ((cs.extract start j).toList))
        i := j
  return out

structure PState where
  toks : Array String
  pos : Nat := 0
deriving Inhabited

abbrev ParserM := Except String

def PState.peek? (p : PState) : Option String := p.toks[p.pos]?
def PState.bump (p : PState) : PState := { p with pos := p.pos + 1 }

def expect (p : PState) (tok : String) : ParserM PState :=
  match p.peek? with
  | some t => if t == tok then pure p.bump else throw s!"expected '{tok}', got '{t}'"
  | none => throw s!"expected '{tok}', got end of input"

def startsAtom : Option String -> Bool
  | some "(" | some "_" | some "Type" | some "Prop" => true
  | some t => !(["=", ":", ":=", ")", "->", "prod", "o"].contains t)
  | none => false

mutual
partial def parseExpr (p : PState) : ParserM (Expr × PState) :=
  parseArrow p

partial def parseArrow (p : PState) : ParserM (Expr × PState) := do
  let (lhs, p) <- parseComp p
  match p.peek? with
  | some "->" =>
      let (rhs, p) <- parseArrow p.bump
      pure (.arrow lhs rhs, p)
  | _ => pure (lhs, p)

partial def parseComp (p : PState) : ParserM (Expr × PState) := do
  let (first, p) <- parseProd p
  let rec loop (acc : Expr) (p : PState) := do
    match p.peek? with
    | some "o" =>
        let (rhs, p) <- parseProd p.bump
        loop (.comp acc rhs) p
    | _ => pure (acc, p)
  loop first p

partial def parseProd (p : PState) : ParserM (Expr × PState) := do
  let (first, p) <- parseApp p
  let rec loop (acc : Expr) (p : PState) := do
    match p.peek? with
    | some "prod" =>
        let (rhs, p) <- parseApp p.bump
        loop (.prod acc rhs) p
    | _ => pure (acc, p)
  loop first p

partial def parseApp (p : PState) : ParserM (Expr × PState) := do
  let (first, p) <- parseAtom p
  let rec loop (acc : Expr) (p : PState) := do
    if startsAtom p.peek? then
      let (arg, p) <- parseAtom p
      loop (.app acc arg) p
    else
      pure (acc, p)
  loop first p

partial def parseAtom (p : PState) : ParserM (Expr × PState) := do
  match p.peek? with
  | some "(" =>
      let (e, p) <- parseExpr p.bump
      let p <- expect p ")"
      pure (e, p)
  | some "_" => pure (.hole, p.bump)
  | some "Type" => pure (.sortType, p.bump)
  | some "Prop" => pure (.sortProp, p.bump)
  | some t =>
      if ["=", ":", ":=", ")", "->", "prod", "o"].contains t then
        throw s!"expected expression, got '{t}'"
      else
        let t := if t.startsWith "@" then (t.drop 1).toString else t
        let n := if t.startsWith "_root_." then "." ++ (t.drop 7).toString else t
        pure (.ident n, p.bump)
  | none => throw "expected expression, got end of input"
end

def parseExprFromTokens (toks : Array String) : ParserM Expr := do
  let (e, p) <- parseExpr { toks := toks }
  if p.pos == toks.size then pure e else throw s!"unexpected token '{p.toks[p.pos]!}'"

partial def parseBinders (toks : Array String) (pos : Nat) : ParserM (Array Param × Nat) := do
  let mut params := #[]
  let mut i := pos
  while i < toks.size && toks[i]! == "(" do
    i := i + 1
    let mut names := #[]
    while i < toks.size && toks[i]! != ":" do
      names := names.push toks[i]!
      i := i + 1
    if i >= toks.size then throw "unterminated binder"
    i := i + 1
    let start := i
    let mut depth := 0
    while i < toks.size && !(depth == 0 && toks[i]! == ")") do
      if toks[i]! == "(" then depth := depth + 1
      else if toks[i]! == ")" then depth := depth - 1
      i := i + 1
    if i >= toks.size then throw "unterminated binder type"
    let ty <- parseExprFromTokens (toks.extract start i)
    for n in names do
      if n != "_" then params := params.push { name := n, type := ty }
    i := i + 1
  pure (params, i)

def parseDecl (line : Nat) (text : String) : ParserM Command := do
  let toks := tokenize text
  let mut i := 0
  let noncomp := toks[i]? == some "noncomputable"
  if noncomp then i := i + 1
  let kindTok <- match toks[i]? with
    | some k => pure k
    | none => throw "empty declaration"
  let kind <- match kindTok with
    | "axiom" => pure DeclKind.axiom
    | "def" => pure DeclKind.defn
    | "abbrev" => pure DeclKind.abbrev
    | _ => throw s!"unknown declaration keyword '{kindTok}'"
  i := i + 1
  let name <- match toks[i]? with
    | some n => pure n
    | none => throw "missing declaration name"
  i := i + 1
  let (params, i') <- parseBinders toks i
  i := i'
  let mut ann : Option Expr := none
  let mut body : Option Expr := none
  if toks[i]? == some ":" then
    i := i + 1
    let start := i
    while i < toks.size && toks[i]! != ":=" do
      i := i + 1
    ann := some (<- parseExprFromTokens (toks.extract start i))
  if toks[i]? == some ":=" then
    i := i + 1
    body := some (<- parseExprFromTokens (toks.extract i toks.size))
  let ty <- match ann, body with
    | some t, _ => pure t
    | none, some b => pure .hole
    | none, none => throw "declaration needs a type or body"
  pure (.declCmd { name, kind, params, type := ty, body })

def startsCommand (s : String) : Bool :=
  let t := s.trimAscii.toString
  ["import ", "open ", "namespace ", "end", "#check", "axiom ", "def ", "abbrev ",
   "noncomputable def ", "noncomputable abbrev "].any (fun p => t.startsWith p)

def commandBlocks (src : String) : Array (Nat × String) := Id.run do
  let clean := stripBlockComments src
  let lines := clean.splitOn "\n" |>.toArray
  let mut out := #[]
  let mut cur := ""
  let mut start := 1
  for h : idx in [0:lines.size] do
    let raw := stripLineComment lines[idx]!
    let t := raw.trimAscii.toString
    if t.isEmpty then
      continue
    if startsCommand t && !cur.isEmpty then
      out := out.push (start, cur)
      cur := t
      start := idx + 1
    else
      if cur.isEmpty then start := idx + 1
      cur := (cur ++ " " ++ t).trimAscii.toString
  if !cur.isEmpty then out := out.push (start, cur)
  out

def parseCommand (line : Nat) (text : String) : ParserM Command := do
  let toks := tokenize text
  match toks[0]? with
  | some "import" =>
      match toks[1]? with | some n => pure (.importCmd n) | none => throw "missing import name"
  | some "open" =>
      match toks[1]? with | some n => pure (.openCmd n) | none => throw "missing open name"
  | some "namespace" =>
      match toks[1]? with | some n => pure (.namespaceCmd n) | none => throw "missing namespace name"
  | some "end" => pure (.endCmd toks[1]?)
  | some "#check" => pure (.checkCmd (<- parseExprFromTokens (toks.extract 1 toks.size)))
  | _ => parseDecl line text

def parseFile (file src : String) : Except Diagnostic (Array (Nat × Command)) := do
  let mut out := #[]
  for (line, text) in commandBlocks src do
    match parseCommand line text with
    | .ok c => out := out.push (line, c)
    | .error e => throw { file, line, message := e }
  pure out

end CoreChecker
