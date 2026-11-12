-- TLDR: `#gold_check` lists every user-written named gold theorem (Gold.*) and checks that its bridge counterpart (Bridge.G_<name>, or Bridge.G_<parent>_<name> when the last component is ambiguous or namespaced) exists, is a theorem and uses only standard axioms.
import Lean
open Lean Meta Elab Command

elab "#gold_check" : command => do
  let env ← getEnv
  -- 1. collect named gold theorems (public, user-written, not structure fields, not nested auxiliaries)
  let mut cands : Array (Name × Name) := #[]
  for (nm, ci) in env.constants.map₁.toList do
    let n' := (privateToUserName? nm).getD nm
    if (`Gold).isPrefixOf n' && (!nm.isInternal || isPrivateName nm) then
      match ci with
      | .thmInfo _ =>
        let aux := match nm.eraseMacroScopes with
          | .str _ l => l.startsWith "match_" || l.startsWith "proof_"
          | _ => false
        if aux then continue
        let rng ← findDeclarationRanges? nm
        if rng.isNone then continue
        if isPrivateName nm then
          logInfo m!"GCHK {n'} PRIVATE_HELPER"
          continue
        let pre := n'.getPrefix
        -- structure field proofs (e.g. `Foo.nonempty` of a structure field) are not named theorems
        match getStructureInfo? env pre with
        | some si =>
          if si.fieldNames.contains (match n' with | .str _ s => Name.mkSimple s | _ => Name.anonymous) then
            logInfo m!"GCHK {n'} STRUCTURE_FIELD"
            continue
        | none => pure ()
        -- nested auxiliary (let rec / local lemma lifted out of another declaration)
        match env.find? pre with
        | some (.thmInfo _) | some (.defnInfo _) =>
          logInfo m!"GCHK {n'} NESTED_AUX"
          continue
        | _ => pure ()
        cands := cands.push (nm, n')
      | _ => pure ()
    else pure ()
  let lastOf := fun (n : Name) => match n with | .str _ s => s | _ => n.toString
  let lasts := cands.map (fun p => lastOf p.2)
  let mut okc := 0
  for (nm, n') in cands do
    let l := lastOf n'
    let dupl := (lasts.filter (· == l)).size > 1
    let parentLast := match n'.getPrefix with | .str _ s => s | _ => ""
    let plain := Name.mkStr `Bridge ("G_" ++ l)
    let qual := Name.mkStr `Bridge ("G_" ++ parentLast ++ "_" ++ l)
    let b? := if dupl then (if (env.find? qual).isSome then some qual else none)
              else if (env.find? plain).isSome then some plain
              else if (env.find? qual).isSome then some qual else none
    match b? with
    | none => logInfo m!"GCHK {n'} MISSING"
    | some b =>
      match env.find? b with
      | some (.thmInfo _) =>
        let ax ← liftCoreM <| collectAxioms b
        let bad := ax.filter (fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound))
        if bad.size > 0 then logInfo m!"GCHK {n'} NONSTD {bad}"
        else
          okc := okc + 1
          logInfo m!"GCHK {n'} OK {b}"
      | _ => logInfo m!"GCHK {n'} NOT_THEOREM"
  logInfo m!"GSUMMARY gold={cands.size} proved={okc} dup_last_components=0"
