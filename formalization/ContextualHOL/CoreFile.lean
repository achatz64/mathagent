import CoreChecker.Checker

/-! Recursive source loading for the native checker.  This module belongs to
the input boundary only: quoted contextual environments do not retain any of
these expressions. -/

namespace ContextualHOL.ProgramC.CoreFile

open CoreChecker

structure LoadState where
  env : CoreChecker.Env := {}
  checked : Std.HashSet String := {}

inductive LoadError where
  | io (message : String)
  | parse (diagnostic : Diagnostic)
  | missingImport (fromFile moduleName : String)
  deriving Repr

def pathDir (path : String) : String :=
  let parts := path.splitOn "/"
  match parts.reverse with
  | [] | [_] => "."
  | _ :: rest =>
      let dir := "/".intercalate rest.reverse
      if dir.isEmpty then "/" else dir

def joinPath (dir relative : String) : String :=
  if dir.isEmpty || dir == "." then relative else dir ++ "/" ++ relative

def moduleRelPath (name : String) : String :=
  "/".intercalate (name.splitOn ".") ++ ".cor"

def importsOf (commands : Array (Nat × Command)) : Array Name :=
  commands.foldl (fun out item => match item.2 with
    | .importCmd name => out.push name
    | _ => out) #[]

partial def firstReadable : List String -> IO (Option String)
  | [] => pure none
  | path :: rest => do
      if ← System.FilePath.pathExists ⟨path⟩ then pure (some path)
      else firstReadable rest

partial def loadOne (roots : List String) (state : LoadState)
    (file : String) : ExceptT LoadError IO LoadState := do
  if state.checked.contains file then pure state
  else
    let source ← IO.FS.readFile file
    let commands ← match parseFile file source with
      | .ok commands => pure commands
      | .error diagnostic => throw (.parse diagnostic)
    let mut current := state
    for imported in importsOf commands do
      let relative := moduleRelPath imported
      let candidates := joinPath (pathDir file) relative ::
        roots.map (fun root => joinPath root relative)
      let dependency ← match ← firstReadable candidates with
        | some dependency => pure dependency
        | none => throw (.missingImport file imported)
      current ← loadOne roots current dependency
    match checkCommandsIn current.env file commands with
    | .ok env =>
        pure { env, checked := current.checked.insert file }
    | .error diagnostic => throw (.parse diagnostic)

def load (roots : List String) (file : String) : ExceptT LoadError IO CoreChecker.Env := do
  pure (← loadOne roots {} file).env

end ContextualHOL.ProgramC.CoreFile
