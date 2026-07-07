import CoreChecker.Checker

open CoreChecker

def printDiag (d : Diagnostic) : IO Unit := do
  IO.eprintln s!"{d.file}:{d.line}: {d.message}"

structure RunState where
  env : Env := {}
  checked : Std.HashSet String := {}
  failed : Bool := false

def pathDir (path : String) : String :=
  let parts := path.splitOn "/"
  match parts.reverse with
  | [] => "."
  | _ :: [] => "."
  | _ :: rest =>
      let dir := "/".intercalate rest.reverse
      if dir.isEmpty then "/" else dir

def joinPath (dir rel : String) : String :=
  if dir.isEmpty || dir == "." then rel else dir ++ "/" ++ rel

def moduleRelPath (name : String) : String :=
  "/".intercalate (name.splitOn ".") ++ ".cor"

def explicitPath (arg : String) : String :=
  if arg.endsWith ".cor" then arg else moduleRelPath arg

partial def firstReadable : List String -> IO (Option String)
  | [] => pure none
  | p :: ps => do
      try
        discard <| IO.FS.readFile p
        pure (some p)
      catch _ =>
        firstReadable ps

def resolveImport (fromFile modName : String) : IO (Option String) := do
  let rel := moduleRelPath modName
  firstReadable [
    joinPath (pathDir fromFile) rel,
    rel,
    joinPath "ma1" rel,
    joinPath "/home/andre/mathagent/ma1" rel
  ]

def importsOf (cmds : Array (Nat × Command)) : Array Name :=
  cmds.foldl
    (fun acc item =>
      match item.2 with
      | .importCmd n => acc.push n
      | _ => acc)
    #[]

partial def checkOne (state : RunState) (file : String) : IO RunState := do
  if state.checked.contains file then
    pure state
  else
    let src <- IO.FS.readFile file
    match parseFile file src with
    | .error d =>
        printDiag d
        pure { state with checked := state.checked.insert file, failed := true }
    | .ok cmds =>
        let mut state := state
        for dep in importsOf cmds do
          match (<- resolveImport file dep) with
          | some depFile =>
              state <- checkOne state depFile
          | none =>
              IO.eprintln s!"{file}: import '{dep}' not found"
              state := { state with failed := true }
        match checkCommandsIn state.env file cmds with
        | .ok env' =>
            IO.println s!"ok {file}"
            pure { state with env := env', checked := state.checked.insert file }
        | .error d =>
            printDiag d
            pure { state with checked := state.checked.insert file, failed := true }

partial def checkFiles (state : RunState) : List String -> IO RunState
  | [] => pure state
  | file :: rest => do
      let state <- checkOne state (explicitPath file)
      checkFiles state rest

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.eprintln "usage: corecheck FILE.cor ..."
    IO.Process.exit 2
  let state <- checkFiles {} args
  if state.failed then
    throw (IO.userError "corecheck failed")
