/-
Supplemental syntax extractor for the structural commands transformed in
Phase 4 of references/upload_full_project.md. It reports exact parser ranges
for namespace/section/end/include commands; consumers must never rediscover
these commands by searching source text.

Run:
  lake env lean --run prove2me/tools/extract_context_info.lean <File.lean>
-/
import Lean

open Lean Elab Parser

partial def findKind? (stx : Syntax) (kind : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == kind then some stx
  else stx.getArgs.findSome? (findKind? · kind)

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [
    ("line", toJson pos.line),
    ("col", toJson pos.column),
    ("offset", toJson p.byteIdx)
  ]

def rangeJson (fm : FileMap) (stx : Syntax) : Json :=
  match stx.getPos?, stx.getTailPos? with
  | some start, some stop => Json.mkObj [
      ("start", posJson fm start),
      ("end", posJson fm stop)
    ]
  | _, _ => Json.null

partial def collectIdents (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if stx.isIdent then acc.push stx else acc
  stx.getArgs.foldl (fun found child => collectIdents child found) acc

partial def collectAtoms (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if stx.isAtom then acc.push stx else acc
  stx.getArgs.foldl (fun found child => collectAtoms child found) acc

def declarationKeyword? (command : Syntax) (declId : Syntax) : Option Syntax :=
  match declId.getPos? with
  | none => none
  | some nameStart =>
      collectAtoms command |>.foldl (init := none) fun best atom =>
        let value := atom.getAtomVal
        if value != "theorem" && value != "lemma" && value != "instance" then
          best
        else
          match atom.getPos?, atom.getTailPos? with
          | some start, some stop =>
              if stop > nameStart then best
              else match best with
                | none => some atom
                | some previous =>
                    if previous.getPos?.getD start < start then some atom else best
          | _, _ => best

def declarationIsLocal (command : Syntax) (keyword : Syntax) : Bool :=
  match keyword.getPos? with
  | none => false
  | some keywordStart =>
      collectAtoms command |>.any fun atom =>
        atom.getAtomVal == "local" && atom.getTailPos?.any (· <= keywordStart)

def anonymousInstanceHead? (command : Syntax) : Option (Syntax × String.Pos.Raw) := do
  let instanceStx ← findKind? command ``Command.instance
  if (findKind? instanceStx ``Command.declId).isSome then
    none
  else
    let keyword ← collectAtoms instanceStx |>.find? (·.getAtomVal == "instance")
    let insertPos ←
      match findKind? instanceStx ``Command.namedPrio with
      | some priority => priority.getTailPos?
      | none => keyword.getTailPos?
    return (keyword, insertPos)

def printDeclHead (fm : FileMap) (command keyword : Syntax)
    (nameInsert? : Option String.Pos.Raw := none) : IO Unit := do
  let some start := command.getPos? | return
  let some stop := command.getTailPos? | return
  IO.println (Json.mkObj [
    ("kind", Json.str "declHead"),
    ("declStart", posJson fm start),
    ("declEnd", posJson fm stop),
    ("keyword", Json.str keyword.getAtomVal),
    ("keywordRange", rangeJson fm keyword),
    ("nameInsert", nameInsert?.map (posJson fm) |>.getD Json.null),
    ("isLocal", Json.bool (declarationIsLocal command keyword)),
    ("protectedTok", (findKind? command ``Command.protected).map (rangeJson fm ·)
      |>.getD Json.null)
  ]).compress

unsafe def main (args : List String) : IO UInt32 := do
  let some fileName := args[0]?
    | do IO.eprintln "usage: extract_context_info.lean <File.lean>"
         return 1
  let input ← IO.FS.readFile (⟨fileName⟩ : System.FilePath)
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let state ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
  if state.commandState.messages.hasErrors then
    for message in state.commandState.messages.toList do
      IO.eprintln (← message.toString)
    return 1
  let fm := inputCtx.fileMap
  for command in state.commands do
    if let some declId := findKind? command ``Command.declId then
      if let some keyword := declarationKeyword? command declId then
        printDeclHead fm command keyword
    else if let some (keyword, nameInsert) := anonymousInstanceHead? command then
      printDeclHead fm command keyword (some nameInsert)
    if command.isOfKind ``Command.open then
      for ident in collectIdents command do
        IO.println (Json.mkObj [
          ("kind", Json.str "openName"),
          ("name", Json.str ident.getId.toString),
          ("range", rangeJson fm ident)
        ]).compress
    let fields? : Option (List (String × Json)) :=
      if command.isOfKind ``Command.namespace then
        some [("kind", Json.str "namespace"),
          ("name", Json.str command[1].getId.toString),
          ("range", rangeJson fm command)]
      else if command.isOfKind ``Command.section then
        some [("kind", Json.str "section"), ("range", rangeJson fm command)]
      else if command.isOfKind ``Command.end then
        some [("kind", Json.str "end"), ("range", rangeJson fm command)]
      else if command.isOfKind ``Command.include then
        some [("kind", Json.str "include"), ("range", rangeJson fm command)]
      else if command.isOfKind ``Command.export then
        some [("kind", Json.str "dropCommand"), ("range", rangeJson fm command)]
      else
        none
    if let some fields := fields? then
      IO.println (Json.mkObj fields).compress
  return 0
