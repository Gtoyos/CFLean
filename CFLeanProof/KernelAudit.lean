import CFLeanProof
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Exhaustive, failing audit of the project.

Every file under `CFLeanProof/` other than the two audit entry points must be
imported, directly or transitively, by `CFLeanProof.lean`, so that `lake build`
compiles it and this audit sees its declarations. Every declaration under
`ConflictFreedom.` must then depend on no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`. New modules and declarations are included
automatically. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- This file sits in `CFLeanProof/`, next to the modules it checks.
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let auditFiles := [`CFLeanProof.Audit, `CFLeanProof.KernelAudit]
  let imported := env.allImportedModuleNames
  let mut modules : Nat := 0
  for path in ← dir.walkDir do
    unless path.extension == some "lean" do continue
    let parts := (path.withExtension "").components.drop dir.components.length
    let module := parts.foldl Name.str `CFLeanProof
    if auditFiles.contains module then continue
    modules := modules + 1
    unless imported.contains module do
      throwError "{module} is not imported by CFLeanProof.lean"
  if modules == 0 then
    throwError "No modules found in {dir}"
  let mut total : Nat := 0
  for (name, info) in env.constants.toList do
    unless name.toString.startsWith "ConflictFreedom." do continue
    total := total + 1
    match info with
    | .axiomInfo _ => throwError "Project axiom: {name}"
    | _ => pure ()
    for axiomName in ← liftCoreM (Lean.collectAxioms name) do
      unless axiomName == ``propext || axiomName == ``Classical.choice ||
          axiomName == ``Quot.sound do
        throwError "{name} depends on unexpected axiom {axiomName}"
  logInfo m!"Kernel audit passed: {modules} modules, all imported by CFLeanProof.lean; \
    {total} project declarations; only standard Lean axioms."
