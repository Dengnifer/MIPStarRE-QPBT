import Lean

open Lean Parser

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [
    ("line", toJson pos.line),
    ("col", toJson pos.column),
    ("offset", toJson p.byteIdx)
  ]

def syntaxRangeJson (fm : FileMap) (stx : Syntax) : Json :=
  match stx.getPos?, stx.getTailPos? with
  | some start, some stop => Json.mkObj [
      ("start", posJson fm start),
      ("end", posJson fm stop)
    ]
  | _, _ => Json.null

unsafe def emitHeaderFacts (fileName : String) : IO Bool := do
  let input ← IO.FS.readFile (⟨fileName⟩ : System.FilePath)
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    for message in messages.toList do
      IO.eprintln (← message.toString)
    return false
  let fm := inputCtx.fileMap
  let withSource (fields : List (String × Json)) : Json :=
    Json.mkObj (("source", Json.str fileName) :: fields)
  IO.println <| (withSource [
    ("kind", Json.str "header"),
    ("end", posJson fm parserState.pos)
  ]).compress
  if let `(Module.header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $importsStx*) := header then
    if let some moduleTk := moduleTk? then
      IO.println <| (withSource [
        ("kind", Json.str "moduleToken"),
        ("range", syntaxRangeJson fm moduleTk)
      ]).compress
    if let some preludeTk := preludeTk? then
      IO.println <| (withSource [
        ("kind", Json.str "preludeToken"),
        ("range", syntaxRangeJson fm preludeTk)
      ]).compress
    for importStx in importsStx do
      if let `(Module.import| $[public%$publicTk?]? $[meta%$metaTk?]? import
          $[all%$allTk?]? $moduleName) := importStx then
        IO.println <| (withSource [
          ("kind", Json.str "import"),
          ("module", Json.str moduleName.getId.toString),
          ("public", toJson publicTk?.isSome),
          ("meta", toJson metaTk?.isSome),
          ("all", toJson allTk?.isSome),
          ("range", syntaxRangeJson fm importStx)
        ]).compress
  return true

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: extract_all_headers.lean <File.lean>..."
    return 1
  Lean.initSearchPath (← Lean.findSysroot)
  for fileName in args do
    unless ← emitHeaderFacts fileName do return 1
  return 0
