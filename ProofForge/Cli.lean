import Lean
import ProofForge.Extract
import ProofForge.Core.IR
import ProofForge.Wasm.Near.Assemble
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Registry

namespace ProofForge.Cli

inductive Command where
  | build
  deriving BEq, Repr, Inhabited

structure Options where
  command : Command := .build
  outDir : System.FilePath := "build/out"
  names : Array String := #[]
  /-- Fully-qualified Lean modules (`MyProgram.Counter`). Overrides in-tree fixture mapping when set. -/
  modules : Array String := #[]
  help : Bool := false
  version : Bool := false

private def usage : String :=
  "pf — ProofForge NEAR compiler\n" ++
    "\n" ++
    "Usage:\n" ++
    "  pf build [--out DIR] [--module MOD] [Program ...]\n" ++
    "  pf --version\n" ++
    "\n" ++
    "build writes Name.wat / Name.wasm (NEAR raw-u64; locked wat2wasm)\n" ++
    "--module takes a dotted Lean module (repeatable). Bare Program names map to in-tree Examples fixtures.\n" ++
    "User projects should pass --module or list [[program]] entries in pf.toml.\n" ++
    "No program names on build means every registered source module.\n"

def parseArgs (args : List String) : Except String Options :=
  let rec go (rest : List String) (o : Options) : Except String Options :=
    match rest with
    | [] => .ok o
    | "-h" :: _ | "--help" :: _ => .ok { o with help := true }
    | "--version" :: _ | "-V" :: _ => .ok { o with version := true }
    | "--target" :: t :: rest =>
      if t == "near" then go rest o
      else if t == "wasm" then
        .error "wasm is a chain family, not a target; this build of pf supports NEAR only"
      else .error s!"unknown target {t} (this build of pf supports NEAR only)"
    | "--out" :: d :: rest => go rest { o with outDir := d }
    | "--module" :: m :: rest => go rest { o with modules := o.modules.push m }
    | flag :: rest =>
      if flag.startsWith "-" then .error s!"unknown flag {flag}"
      else go rest { o with names := o.names.push flag }
  let args := args.dropWhile (· == "--")
  let (_cmd, rest) :=
    match args with
    | "build" :: rest => (Command.build, rest)
    | rest => (Command.build, rest)
  go rest { command := _cmd }

private def nearProgramNames : Array String :=
  Wasm.Near.Registry.names

private def selectNearNames (names : Array String) : Except String (Array String) :=
  if names.isEmpty then .ok nearProgramNames
  else
    names.mapM fun n =>
      match nearProgramNames.find? (· == n) with
      | some _ => .ok n
      | none => .error s!"unknown near program {n}"

/-- Dual-target fixtures stay at `Examples.<Name>`; NEAR-only fixtures live under
`Examples.Near.<Name>`. Program registry names are the last component. -/
private def sharedFixtureNames : Array String :=
  #["Counter", "Flag", "Lang", "Maybe", "Pair", "Phase", "TokenShape", "Window"]

/-- Ergonomics / handle fixtures not yet moved under `Examples.Near.`. -/
private def rootFixtureNames : Array String :=
  #["NearPromiseHandle", "NearTokenErgonomics"]

def fixtureModule (name : String) : Lean.Name :=
  if sharedFixtureNames.contains name || rootFixtureNames.contains name then
    Lean.Name.str `Examples name
  else
    Lean.Name.str `Examples.Near name

structure BuildUnit where
  name : String
  module : Lean.Name
  deriving Repr

private def dottedToName (mod : String) : Lean.Name :=
  (mod.splitOn ".").foldl (fun n p => if p.isEmpty then n else Lean.Name.str n p) .anonymous

private def basenameOfModule (mod : String) : String :=
  match (mod.splitOn ".").getLast? with
  | some n => n
  | none => mod

private def trimStr (s : String) : String :=
  s.trimAscii.toString

private def dropStr (s : String) (n : Nat) : String :=
  (s.drop n).toString

private def dropEndStr (s : String) (n : Nat) : String :=
  (s.dropEnd n).toString

private def unquoteToml (v0 : String) : String :=
  let v := trimStr v0
  if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
    dropEndStr (dropStr v 1) 1
  else if v.startsWith "'" && v.endsWith "'" && v.length ≥ 2 then
    dropEndStr (dropStr v 1) 1
  else v

/-- Value after the first `=` on a TOML assignment line. -/
private def tomlValue (line : String) : Option String :=
  match line.splitOn "=" with
  | _ :: rest =>
    if rest.isEmpty then none
    else some (unquoteToml (String.intercalate "=" rest))
  | _ => none

/-- Minimal `pf.toml` reader: collect `[[program]]` tables with `name` / `module`. -/
private def parsePfTomlPrograms (text : String) : Array BuildUnit := Id.run do
  let mut units : Array BuildUnit := #[]
  let mut inProgram := false
  let mut curName : Option String := none
  let mut curModule : Option String := none
  let flush (units : Array BuildUnit) (curName : Option String) (curModule : Option String) :=
    match curModule with
    | some m =>
      let n := curName.getD (basenameOfModule m)
      units.push { name := n, module := dottedToName m }
    | none => units
  for line0 in text.splitOn "\n" do
    let line := trimStr line0
    if line.isEmpty || line.startsWith "#" then
      pure ()
    else if line == "[[program]]" then
      if inProgram then
        units := flush units curName curModule
      inProgram := true
      curName := none
      curModule := none
    else if inProgram then
      if line.startsWith "name" then
        match tomlValue line with
        | some v => curName := some v
        | none => pure ()
      else if line.startsWith "module" then
        match tomlValue line with
        | some v => curModule := some v
        | none => pure ()
      else if line.startsWith "[" then
        units := flush units curName curModule
        inProgram := false
        curName := none
        curModule := none
  if inProgram then
    units := flush units curName curModule
  units

private def loadPfTomlUnits : IO (Array BuildUnit) := do
  let path : System.FilePath := "pf.toml"
  if !(← path.pathExists) then
    return #[]
  let text ← IO.FS.readFile path
  return parsePfTomlPrograms text

private def resolveUnits (opts : Options)
    (selectNames : Array String → Except String (Array String))
    (tomlUnits : Array BuildUnit) :
    Except String (Array BuildUnit) := do
  if !opts.modules.isEmpty then
    pure <| opts.modules.map fun m =>
      { name := basenameOfModule m, module := dottedToName m }
  else if !opts.names.isEmpty then
    let names ← selectNames opts.names
    pure <| names.map fun n => { name := n, module := fixtureModule n }
  else if !tomlUnits.isEmpty then
    pure tomlUnits
  else
    let names ← selectNames #[]
    pure <| names.map fun n => { name := n, module := fixtureModule n }

private def isExamplesModule : Lean.Name → Bool
  | .str .anonymous "Examples" => true
  | .str pref _ => isExamplesModule pref
  | _ => false

/--
CLI builds must re-extract IR from user modules; never assemble legacy Golden smoke fixtures.
The registry only lists buildable modules and pins canonical digests for Examples fixtures.
-/
private unsafe def extractNearPrograms (units : Array BuildUnit) :
    IO (Except String (Array ProofForge.Wasm.Near.IR.Program)) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let modules := units.map fun u => ({ module := u.module } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return units.mapM fun u =>
      match Extract.extractModuleIR env u.module none >>= Wasm.Near.IR.fromExtracted with
      | .error reason => .error s!"{u.name}: {reason}"
      | .ok program =>
        if !isExamplesModule u.module then
          .ok program
        else
          let digest := Wasm.Near.IR.digestHex program
          match Wasm.Near.Registry.digestOf u.name with
          | some expected =>
            if digest == expected then .ok program
            else .error s!"{u.name}: ir/mismatch: extracted near digest {digest} != fixture {expected}"
          | none => .ok program
  catch e =>
    return .error s!"source import failed: {e}"

private def toolLine (cmd : String) (args : Array String) (fallback : String) : IO String := do
  try
    let proc ← IO.Process.output { cmd := cmd, args := args }
    if proc.exitCode == 0 then
      let line := (trimStr proc.stdout).splitOn "\n" |>.headD (trimStr proc.stdout)
      return if line.isEmpty then fallback else line
    else
      return fallback
  catch _ =>
    return fallback

private def printVersion : IO Unit := do
  IO.println "pf 0.0.1 (ProofForge NEAR)"
  IO.println s!"lean {Lean.versionString}"
  IO.println s!"wat2wasm {(← toolLine "wat2wasm" #["--version"] "1.0.41 (pin; binary not on PATH)")}"
  IO.println "pins: lean v4.31.0; wat2wasm/wabt 1.0.41; near-sandbox 2.13.0"

unsafe def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error reason =>
    IO.eprintln s!"pf: {reason}"
    IO.eprintln usage
    return 1
  | .ok opts =>
    if opts.help then
      IO.println usage
      return 0
    if opts.version then
      printVersion
      return 0
    match opts.command with
    | .build =>
    let tomlUnits ← loadPfTomlUnits
    match resolveUnits opts selectNearNames tomlUnits with
    | .error reason =>
      IO.eprintln s!"pf: {reason}"
      return 1
    | .ok units =>
      match ← extractNearPrograms units with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok programs =>
        IO.FS.createDirAll opts.outDir
        for program in programs do
          let r ← ProofForge.Wasm.Near.Assemble.assembleProgram opts.outDir program
          IO.println s!"wrote {r.watPath} {r.wasmPath} ({r.watSource.length} bytes WAT; deployable=false)"
        return 0

end ProofForge.Cli

unsafe def main (args : List String) : IO UInt32 :=
  ProofForge.Cli.run args
