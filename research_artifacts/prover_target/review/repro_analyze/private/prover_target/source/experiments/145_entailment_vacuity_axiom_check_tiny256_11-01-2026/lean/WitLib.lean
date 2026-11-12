import Mathlib
import Lean
open Lean Meta Elab Term Command

namespace WitLib

def agentConsts : MetaM (Array Name × Array Name) := do
  let env ← getEnv
  let mut defs : Array Name := #[]
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let n' := (privateToUserName? n).getD n
    if (`Agent).isPrefixOf n' && (!n.isInternal || isPrivateName n) then
      let s := n.toString
      if (s.splitOn "match_").length > 1 || (s.splitOn "proof_").length > 1 then continue
      match ci with
      | .defnInfo _ => defs := defs.push n
      | .opaqueInfo _ => defs := defs.push n
      | .thmInfo _ => thms := thms.push n
      | _ => pure ()
  return (defs.qsort (fun a b => a.toString < b.toString), thms.qsort (fun a b => a.toString < b.toString))

def stdOnly (axc : IO.Ref (Std.HashMap Name Bool)) (n : Name) : CoreM Bool := do
  match (← axc.get).get? n with
  | some b => return b
  | none =>
    let ax ← collectAxioms n
    let b := ax.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
    axc.modify (·.insert n b)
    return b

partial def tryClose (axc : IO.Ref (Std.HashMap Name Bool)) (thms : Array Name) (g : MVarId) (fuel : Nat) : MetaM Bool := do
  if fuel == 0 then return false
  g.withContext do
    let s0 ← saveState
    -- assumption
    try
      g.assumption
      return true
    catch _ => s0.restore
    -- apply an agent theorem, close premises
    for t in thms do
      if !(← stdOnly axc t) then continue
      let s ← saveState
      try
        let c ← mkConstWithFreshMVarLevels t
        let gs ← g.apply c
        let mut ok := true
        for g' in gs do
          if !(← g'.isAssigned) then
            if !(← tryClose axc thms g' (fuel - 1)) then
              ok := false
              break
        if ok then return true
        s.restore
      catch _ => s.restore
    -- structure
    let ty ← whnfR (← g.getType)
    match ty with
    | .forallE .. =>
      let (_, g') ← g.intro1
      if ← tryClose axc thms g' fuel then return true
      s0.restore
      return false
    | _ =>
      if ty.isAppOf ``And then
        try
          let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
          for g' in gs do
            if !(← tryClose axc thms g' fuel) then
              s0.restore
              return false
          return true
        catch _ => s0.restore; return false
      else if ty.isAppOf ``Iff then
        try
          let gs ← g.apply (← mkConstWithFreshMVarLevels ``Iff.intro)
          for g' in gs do
            if !(← tryClose axc thms g' fuel) then
              s0.restore
              return false
          return true
        catch _ => s0.restore; return false
      else if ty.isAppOf ``True then
        g.assign (mkConst ``True.intro); return true
      else
        -- last resort: reflexivity
        try
          g.refl
          return true
        catch _ => s0.restore; return false

def constStr (n : Name) : String := n.toString (escape := true)

def fallback (g : MVarId) : TermElabM Bool := do
  let env ← getEnv
  let ty ← instantiateMVars (← g.getType)
  let consts := ty.foldConsts #[] fun c acc =>
    let c' := (privateToUserName? c).getD c
    if (`Agent).isPrefixOf c' || (`Bridge).isPrefixOf c' then acc.push c else acc
  let lemmas := ", ".intercalate (consts.toList.map constStr)
  let lem := if consts.isEmpty then "" else s!" [{lemmas}]"
  let tacs := [s!"intros; simp_all{lem}; done", s!"intros; decide", s!"intros; omega",
    s!"intros; simp_all{lem} <;> omega", s!"intros; split <;> simp_all{lem}",
    s!"intros; aesop (add norm unfold {lemmas})" ]
  for tac in tacs do
    if tac.endsWith "unfold " then continue
    let s ← saveState
    try
      match Parser.runParserCategory env `term ("by " ++ tac) with
      | .ok stx =>
        Term.withoutErrToSorry do
          let _ ← Term.runTactic g stx (kind := Term.TacticMVarKind.term)
          pure ()
        let v ← instantiateMVars (mkMVar g)
        if v.hasSorry || v.hasExprMVar then
          s.restore
        else
          return true
      | .error _ => s.restore
    catch _ => s.restore
  return false

structure Info where
  deepest : Nat := 0
  msg : String := ""

partial def search (ov : Array (Name × Syntax)) (axc : IO.Ref (Std.HashMap Name Bool)) (info : IO.Ref Info) (cache : IO.Ref (Array (Name × Expr))) (defs thms : Array Name) (names : Array Name)
    (T : Expr) (depth : Nat) (acc : Array Expr) : TermElabM (Option (Array Expr)) := do
  let T ← whnfR T
  match T with
  | .forallE n d b _ =>
    if !names.contains n then return some acc
    let fail (why : String) : TermElabM (Option (Array Expr)) := do
      let i ← info.get
      if depth ≥ i.deepest then
        info.set { deepest := depth, msg := s!"{why} binder {n} : {← ppExpr d}" }
      return none
    -- user override for this binder
    for (on, ostx) in ov do
      if on == n then
        let r ← try
            let v ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTermEnsuringType ostx (some d)
            let v ← instantiateMVars v
            if v.hasSorry || v.hasMVar then throwError "override has sorry or mvars"
            pure (some v)
          catch e =>
            info.set { deepest := 100000 + depth, msg := s!"OVERRIDE_ERROR for {n}: {← e.toMessageData.toString}" }
            pure none
        match r with
        | none => return none
        | some v => return ← search ov axc info cache defs thms names (b.instantiate1 v) (depth+1) (acc.push v)
    -- reuse a value found earlier under the same name when its type fits
    for (cn, cv) in (← cache.get) do
      if cn == n then
        let s ← saveState
        try
          if ← isDefEq (← inferType cv) d then
            match ← search ov axc info cache defs thms names (b.instantiate1 cv) (depth+1) (acc.push cv) with
            | some r => return some r
            | none => s.restore
          else s.restore
        catch _ => s.restore
    if ← isProp d then
      let m ← mkFreshExprMVar d
      let ok ← (tryClose axc thms m.mvarId! 3) <||> (fallback m.mvarId!)
      if ok then
        let m' ← instantiateMVars m
        cache.modify (·.push (n, m'))
        search ov axc info cache defs thms names (b.instantiate1 m') (depth+1) (acc.push m')
      else fail "HYP_NOT_PROVED"
    else
      for c in defs do
        let s ← saveState
        try
          let ce ← mkConstWithFreshMVarLevels c
          let ct ← inferType ce
          if ← isDefEq ct d then
            let saved ← cache.get
            cache.modify (·.push (n, ce))
            match ← search ov axc info cache defs thms names (b.instantiate1 ce) (depth+1) (acc.push ce) with
            | some r => return some r
            | none => cache.set saved; s.restore
          else s.restore
        catch _ => s.restore
      fail "NO_DEF"
  | _ => return some acc

def runWitness (thmIds : Array (TSyntax `ident)) (names : Array Name) (ov : Array (Name × Syntax)) : CommandElabM Unit := do
  liftTermElabM do
    let (defs, thms') ← agentConsts
    let cache ← IO.mkRef (#[] : Array (Name × Expr))
    let axc ← IO.mkRef ({} : Std.HashMap Name Bool)
    for thm in thmIds do
      let tn ← realizeGlobalConstNoOverloadWithInfo thm
      let ci ← getConstInfo tn
      let info ← IO.mkRef ({} : Info)
      try
        match ← search ov axc info cache defs thms' names ci.type 0 #[] with
        | some acc =>
          let val ← instantiateMVars (mkAppN (mkConst tn) acc)
          if val.hasMVar then
            logError m!"WITNESS_FAIL {tn} mvars left"
            continue
          let ty ← inferType val
          let wn := Name.mkSimple ("Witness_" ++ tn.toString.replace "." "_")
          addDecl (Declaration.thmDecl { name := wn, levelParams := [], type := ty, value := val })
          let used ← acc.filterM (fun e => do return !(← isProp (← inferType e)))
          logInfo m!"WITNESS_OK {tn} as {wn}; functions: {used}"
        | none =>
          let i ← info.get
          logError m!"WITNESS_FAIL {tn}: {i.msg}"
      catch e =>
        logError m!"WITNESS_FAIL {tn}: {e.toMessageData}"

elab "#witness " thms:ident* " [" names:ident,* "]" : command => do
  runWitness thms (names.getElems.map (·.getId)) #[]

elab "#witness_with " thms:ident* " [" names:ident,* "]" " with " ovs:(" (" ident " := " term ")")* : command => do
  let mut ov : Array (Name × Syntax) := #[]
  let flat : Array Syntax := ovs.raw.foldl (fun acc o => if o.getNumArgs == 5 then acc ++ o.getArgs else acc.push o) #[]
  let mut i := 0
  while i + 4 < flat.size + 0 do
    ov := ov.push (flat[i+1]!.getId, flat[i+3]!)
    i := i + 5
  runWitness thms (names.getElems.map (·.getId)) ov

end WitLib
