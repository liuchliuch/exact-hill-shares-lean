import Lean
import Lean.Util.CollectAxioms
import Lean.Replay

/-!
Independent environment audit. Project declarations are selected by their
originating module index, never by their printed namespace. This includes
private names, generated auxiliaries, equations, recursors and unused axioms.

Run with `lake env lean --run scripts/AuditOrigins.lean -- Module.Name ...`.
`--replay-all` rechecks all safe, non-partial imported declarations from a fresh
kernel environment. Otherwise project declarations are replayed against the
imported non-project dependencies. `--axioms-only` omits replay (for diagnostics).
`--safe-declarations` keeps the complete inventory but enforces the axiom whitelist
only on non-unsafe declarations. Lean4.19's old compiler stores unsafe IR axioms
and proof-erasure placeholders in ordinary executable-module object files.

This is verification machinery, not a theorem about Hill shares. Lean's replay
API deliberately skips unsafe/partial executable declarations; counts are
reported explicitly. Transitive axiom checks still examine every project origin.
-/

open Lean

namespace AuditOrigins

-- Use the exact recursive collector underlying `Lean.collectAxioms`, sharing
-- its visited set across roots in one safety class. This computes the union of
-- all transitive dependencies without traversing the same Mathlib proof 1900
-- times. Safe and unsafe roots have separate states, so visiting compiler IR
-- can never suppress a dependency check for a safe theorem.
private def collectOrigin (env : Environment) (decl : Name)
    (state : Lean.CollectAxioms.State) : Lean.CollectAxioms.State :=
  ((Lean.CollectAxioms.collect decl).run env |>.run state).2

private def allowedAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

private def kind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def origin (env : Environment) (decl : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? decl
  env.header.moduleNames[idx.toNat]?

private def asImports (modules : Array Name) : Array Import :=
  modules.map fun name => { module := name }

/-- Lean4.19's public replay implementation queries constructors/recursors via
the elaborator view. That view can miss checked declarations in the kernel's
stage-2 map and nested auxiliaries. Use the official replay operations, then
perform the identical constructor/recursor equality comparisons directly against
the checked kernel environment, which searches both stages. No check is omitted. -/
private def replayChecked (newConstants : Std.HashMap Name ConstantInfo)
    (env : Environment) : IO Environment := do
  let mut remaining : NameSet := {}
  for (name, info) in newConstants.toList do
    if !info.isUnsafe && !info.isPartial then
      remaining := remaining.insert name
  let action : Environment.Replay.M Unit := do
    for name in remaining do
      Environment.Replay.replayConstant name
    modify fun state => { state with
      env := Environment.ofKernelEnv state.env.toKernelEnv }
    for name in (← get).postponedConstructors do
      match (← get).env.toKernelEnv.find? name, newConstants[name]? with
      | some (.ctorInfo actual), some (.ctorInfo stored) =>
        unless actual == stored do
          throw <| IO.userError s!"Invalid constructor {name}"
      | _, _ => throw <| IO.userError s!"No such checked constructor {name}"
    for name in (← get).postponedRecursors do
      match (← get).env.toKernelEnv.find? name, newConstants[name]? with
      | some (.recInfo actual), some (.recInfo stored) =>
        unless actual == stored do
          throw <| IO.userError s!"Invalid recursor {name}"
      | _, _ => throw <| IO.userError s!"No such checked recursor {name}"
  let (_, state) ← (action.run { newConstants }).run { env, remaining }
  unless state.remaining.isEmpty && state.pending.isEmpty do
    throw <| IO.userError "Kernel replay left unprocessed or pending declarations"
  return state.env

def audit (args : List String) : IO UInt32 := do
  let replayAll := args.contains "--replay-all"
  let axiomsOnly := args.contains "--axioms-only"
  let safeOnly := args.contains "--safe-declarations"
  let modules := (args.filter fun arg => !arg.startsWith "--").toArray.map String.toName
  if modules.isEmpty then
    IO.eprintln "Usage: AuditOrigins.lean [--replay-all | --axioms-only] Module.Name ..."
    return 2
  for arg in args do
    if arg.startsWith "--" && arg != "--replay-all" && arg != "--axioms-only" &&
        arg != "--safe-declarations" then
      throw <| IO.userError s!"Unrecognized audit option: {arg}"
  if replayAll && axiomsOnly then
    throw <| IO.userError "Choose either --replay-all or --axioms-only, not both"
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (asImports modules) {} (trustLevel := 0)
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throw <| IO.userError s!"Requested module was not imported: {mod}"
  let root ← IO.FS.realPath (← IO.currentDir)
  let localBuild := (root / ".lake" / "build" / "lib" / "lean").toString ++ "/"
  let freshBuild := (root / ".lake" / "audit").toString ++ "/"
  for mod in env.header.moduleNames do
    let path := (← IO.FS.realPath (← Lean.findOLean mod)).toString
    if (path.startsWith localBuild || path.startsWith freshBuild) && !modules.contains mod then
      throw <| IO.userError s!"Imported local module {mod} is missing from the origin inventory"
  let mut project : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    unless name == info.name do
      throw <| IO.userError s!"Malformed constant-map key/name mismatch: {name} vs {info.name}"
    if let some mod := origin env name then
      if modules.contains mod then
        project := project.push (name, info)
  let mut metadataOnly : Array (Name × Name) := #[]
  for (name, idx) in env.const2ModIdx.toList do
    if let some mod := env.header.moduleNames[idx.toNat]? then
      if modules.contains mod && (env.toKernelEnv.find? name).isNone then
        metadataOnly := metadataOnly.push (mod, name)
  project := project.qsort fun a b => a.1.toString < b.1.toString
  if project.isEmpty then
    throw <| IO.userError "Origin selection was empty; refusing a vacuous success"
  IO.println s!"AUDIT_MODULES\t{String.intercalate "," (modules.toList.map toString)}"
  IO.println s!"IMPORTED_MODULE_COUNT\t{env.header.moduleNames.size}"
  IO.println s!"ORIGIN_DECLARATION_COUNT\t{project.size}"
  IO.println s!"ORIGIN_METADATA_WITHOUT_DECLARATION_COUNT\t{metadataOnly.size}"
  for (mod, name) in metadataOnly do
    IO.println s!"COMPILER_NAME_METADATA_ONLY\t{mod}\t{name}"
  IO.println s!"WHITELIST_SCOPE\t{if safeOnly then "all-non-unsafe-origins; unsafe compiler IR inventoried separately" else "all-origin-constants-strict"}"
  IO.println "module\tdeclaration\tkind\tsafety\tnew_axioms_in_safety_class_union"
  let mut failures := 0
  let mut theorems := 0
  let mut unsafeOrigins := 0
  let mut partialOrigins := 0
  let mut safeState : Lean.CollectAxioms.State := {}
  let mut unsafeState : Lean.CollectAxioms.State := {}
  for (name, info) in project do
    let mod := (origin env name).getD .anonymous
    let prior := if info.isUnsafe then unsafeState else safeState
    let next := collectOrigin env name prior
    let axioms := (next.axioms.extract prior.axioms.size next.axioms.size).qsort fun a b => a.toString < b.toString
    if info.isUnsafe then unsafeState := next else safeState := next
    let unexpected := axioms.filter fun a => !allowedAxiom a
    let safety := if info.isUnsafe then "unsafe" else if info.isPartial then "partial" else "safe"
    IO.println s!"{mod}\t{name}\t{kind info}\t{safety}\t{String.intercalate "," (axioms.toList.map toString)}"
    if info.isUnsafe then
      unsafeOrigins := unsafeOrigins + 1
    if info.isPartial then
      partialOrigins := partialOrigins + 1
    if info matches .thmInfo _ then
      theorems := theorems + 1
    if !unexpected.isEmpty && !(safeOnly && info.isUnsafe) then
      IO.eprintln s!"FORBIDDEN_AXIOMS\t{name}\t{unexpected}"
      failures := failures + 1
  IO.println s!"ORIGIN_THEOREM_COUNT\t{theorems}"
  IO.println s!"UNSAFE_ORIGIN_COUNT\t{unsafeOrigins}"
  IO.println s!"PARTIAL_ORIGIN_COUNT\t{partialOrigins}"
  IO.println s!"SAFE_TRANSITIVE_AXIOM_UNION\t{safeState.axioms}"
  IO.println s!"UNSAFE_TRANSITIVE_AXIOM_UNION\t{unsafeState.axioms}"
  IO.println s!"UNSAFE_NONFOUNDATIONAL_AXIOM_COUNT\t{(unsafeState.axioms.filter fun a => !allowedAxiom a).size}"
  if failures != 0 then
    IO.eprintln s!"AXIOM_AUDIT_FAILED\t{failures} declarations"
    return 1
  IO.println s!"AXIOM_AUDIT_PASSED\tscope={if safeOnly then "all-non-unsafe-origins" else "all-origin-constants"}\tallowed only propext,Classical.choice,Quot.sound"
  if axiomsOnly then
    IO.println "KERNEL_REPLAY_NOT_REQUESTED"
    return 0
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut skipped := 0
  if replayAll then
    for (name, info) in env.constants.toList do
      replayMap := replayMap.insert name info
      if info.isUnsafe || info.isPartial then
        skipped := skipped + 1
  else
    for (name, info) in project do
      replayMap := replayMap.insert name info
      if info.isUnsafe || info.isPartial then
        IO.println s!"PROJECT_EXECUTABLE_REPLAY_SKIP\t{name}"
        skipped := skipped + 1
  IO.println s!"KERNEL_REPLAY_BEGIN\tmode={if replayAll then "all-imports" else "project-origins"}\tdeclarations={replayMap.size}\tunsafe-or-partial-skipped={skipped}"
  let base ← if replayAll then
      Lean.mkEmptyEnvironment 0
    else
      Lean.importModules
        (asImports (env.header.moduleNames.filter fun mod => !modules.contains mod))
        {} (trustLevel := 0)
  -- The non-project import closure must not accidentally contain an audited
  -- module (e.g. through a helper omitted from the module list).
  if !replayAll then
    for mod in modules do
      if base.header.moduleNames.contains mod then
        throw <| IO.userError s!"Project module {mod} leaked into replay base; provide the complete local module inventory"
  -- Replay module-by-module, in the import topological order. Lean4.19's
  -- elaborator tracks private names after stripping their module prefix; one
  -- giant replay causes collisions between unrelated modules' `_proof_1`,
  -- splitters, etc. Checkpointing only the already-checked kernel environment
  -- resets that elaborator bookkeeping without trusting any new declaration.
  let mut perModule : Std.HashMap Name (Std.HashMap Name ConstantInfo) := {}
  for (name, info) in replayMap.toList do
    let some mod := origin env name
      | throw <| IO.userError s!"Cannot determine replay origin of {name}"
    let group := (perModule[mod]?).getD {}
    perModule := perModule.insert mod (group.insert name info)
  let mut checked := base
  let mut replayedModules := 0
  for mod in env.header.moduleNames do
    if let some group := perModule[mod]? then
      checked ← replayChecked group checked
      checked := Environment.ofKernelEnv checked.toKernelEnv
      replayedModules := replayedModules + 1
      IO.println s!"KERNEL_MODULE_REPLAYED\t{mod}\t{group.size}"
  unless replayedModules == perModule.size do
    throw <| IO.userError "Some origin modules were omitted from the replay traversal"
  IO.println "KERNEL_REPLAY_PASSED"
  return 0

end AuditOrigins

def main (args : List String) : IO UInt32 := AuditOrigins.audit args
