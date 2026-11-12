/- TLDR: Trusted kernel replay: read a candidate .olean as data (never import it) and re-add every one of its constants through the kernel into the trusted environment, then check the target's exact type and transitive axioms there. -/
import Lean
open Lean Elab Command Term Meta

namespace VB169Strict

structure ReplayReport where
  nonce : String
  name : String
  olean : String
  candidateImports : Array String
  candidateConstants : Nat
  skippedUnsafeOrPartial : Nat
  extensionEntries : Nat
  collisions : Array String
  replayed : Bool
  isTheorem : Bool
  typeExact : Bool
  typeDefEq : Bool
  axioms : Array String
  error : String
  deriving ToJson

def emit (r : ReplayReport) : CommandElabM Unit :=
  logInfo m!"VB169_STRICT_KERNEL_REPLAY_JSON {(toJson r).compress}"

/-- Replay the module's constants into `env` (a copy) with kernel checking; `Environment.replay`
calls `addDeclCore` with `doCheck := true` for every definition, theorem, axiom, opaque and
inductive, and only compares stored constructors/recursors against regenerated ones. -/
def replayInto (env : Environment) (md : ModuleData) : IO Environment := do
  let m : Std.HashMap Name ConstantInfo := md.constants.foldl (init := {}) fun acc c => acc.insert c.name c
  env.replay m

end VB169Strict

/-- `#vb_strict_kernel_replay "<nonce>" "<absolute path to Candidate.olean>" name : expectedType`
Must be run in a process whose LEAN_PATH cannot resolve the candidate module; the trusted
environment is the current one (Context and its imports). -/
elab "#vb_strict_kernel_replay " nonce:str olean:str n:ident " : " expected:term : command => do
  let env ← getEnv
  let target := n.getId
  let base : VB169Strict.ReplayReport :=
    { nonce := nonce.getString, name := target.toString, olean := olean.getString,
      candidateImports := #[], candidateConstants := 0, skippedUnsafeOrPartial := 0,
      extensionEntries := 0, collisions := #[], replayed := false, isTheorem := false,
      typeExact := false, typeDefEq := false, axioms := #[], error := "" }
  let reject (r : VB169Strict.ReplayReport) (msg : String) : CommandElabM Unit := do
    VB169Strict.emit { r with error := msg }
    throwError "kernel replay rejected: {msg}"
  if env.contains target then
    reject base "target name already present in the trusted environment"
    return
  -- Read the candidate module as data only.
  let (md, _region) ← liftCoreM (readModuleData ⟨olean.getString⟩ : IO _)
  let imports := md.imports.map (·.module.toString)
  let skipped := (md.constants.filter fun c => c.isUnsafe || c.isPartial).size
  let collisions := md.constants.filterMap fun c => if env.contains c.name then some c.name.toString else none
  let base := { base with
    candidateImports := imports
    candidateConstants := md.constants.size
    skippedUnsafeOrPartial := skipped
    extensionEntries := md.entries.size
    collisions := collisions }
  if !collisions.isEmpty then
    reject base "candidate module redefines names already present in the trusted environment"
    return
  -- The user's source-level rule forbids added axioms even when the target does not use them.
  let addedAxioms := md.constants.filterMap fun c =>
    match c with | .axiomInfo _ => some c.name.toString | _ => none
  if !addedAxioms.isEmpty then
    reject base s!"candidate module adds forbidden axioms: {addedAxioms.toList}"
    return
  -- Kernel replay of the whole candidate constant set into a copy of the trusted environment.
  let replayed? : Except String Environment ← liftCoreM do
    try
      let env' ← (VB169Strict.replayInto env md : IO Environment)
      pure (.ok env')
    catch e =>
      pure (.error (← e.toMessageData.toString))
  match replayed? with
  | .error msg => reject base s!"kernel rejected a candidate declaration: {msg}"
  | .ok env' =>
    let base := { base with replayed := true }
    let some ci := env'.find? target
      | reject base "target absent after replay"
    let isThm := match ci with | .thmInfo _ => true | _ => false
    let wanted ← liftTermElabM do
      let e ← elabType expected
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let typeExact := ci.type == wanted
    let typeDefEq ← liftTermElabM do
      try isDefEq ci.type wanted catch _ => pure false
    let (_, s) := ((CollectAxioms.collect target).run env').run {}
    let report := { base with
      isTheorem := isThm
      typeExact := typeExact
      typeDefEq := typeDefEq
      axioms := s.axioms.map (·.toString) }
    if !isThm then
      reject report "target is not a theorem after replay"
      return
    if !typeExact then
      reject report "target type differs from the immutable expected type"
      return
    VB169Strict.emit report
