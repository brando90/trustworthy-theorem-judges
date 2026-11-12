import Mathlib
import Lean
open Lean Meta Elab Term Command

elab "#agent_axioms" : command => do
  let env ← getEnv
  let mut n := 0
  let mut bad := 0
  for (nm, ci) in env.constants.map₁.toList do
    let n' := (privateToUserName? nm).getD nm
    if (`Agent).isPrefixOf n' && (!nm.isInternal || isPrivateName nm) then
      match ci with
      | .thmInfo _ =>
        let s := nm.toString
        let aux := match nm.eraseMacroScopes with
          | .str _ l => l.startsWith "match_" || l.startsWith "proof_"
          | _ => false
        if aux then continue
        n := n + 1
        let ax ← liftCoreM <| collectAxioms nm
        let nonstd := ax.filter (fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound))
        if nonstd.size > 0 then
          bad := bad + 1
          logInfo m!"AX_NONSTD {nm} {nonstd}"
      | _ => pure ()
  logInfo m!"AX_SUMMARY thms={n} nonstd={bad}"
