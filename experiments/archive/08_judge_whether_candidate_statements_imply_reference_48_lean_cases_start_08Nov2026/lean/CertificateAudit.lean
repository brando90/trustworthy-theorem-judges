import Lean

open Lean Elab Command Term

/-- Elaborate exactly one proof term, never an arbitrary sequence of commands. -/
syntax "certificate " ident " : " term " := " str : command
elab_rules : command
  | `(certificate $n:ident : $ty:term := $body:str) => do
    let env ← getEnv
    match Parser.runParserCategory env `term body.getString with
    | .error msg => throwError "Expected exactly one proof term: {msg}"
    | .ok parsed =>
      let proof : TSyntax `term := ⟨parsed⟩
      elabCommand (← `(theorem $n : $ty := $proof))

/-- Trusted audit: checked environment, exact type, kernel replay, transitive axioms. -/
syntax "#audit_certificate " str ident " : " term : command
elab_rules : command
  | `(#audit_certificate $nonce:str $n:ident : $ty:term) => do
    let expected ← liftTermElabM <| do
      let e ← elabTerm ty none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let env ← getEnv
    let name := n.getId
    let some (.thmInfo info) := env.checked.get.find? name
      | throwError "Certificate is not a kernel-checked theorem"
    match Kernel.isDefEq env {} info.type expected with
    | .ok true => pure ()
    | _ => throwError "Certificate has the wrong exact goal"
    let replayName := Name.str name ("kernelReplay_" ++ nonce.getString)
    match env.addDeclCore 40000000 (.thmDecl { info with name := replayName }) none true with
    | .error _ => throwError "Kernel replay rejected"
    | .ok _ => pure ()
    let axioms ← collectAxioms name
    let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom: {ax}"
    let record := Json.mkObj [
      ("nonce", toJson nonce.getString),
      ("claim", toJson name.toString),
      ("exact_goal", toJson true),
      ("kernel_replayed", toJson true),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"TTJ07_CERTIFICATE_AUDIT {record.compress}"
