/- TLDR: Experiment 117 phase-0 harness: turns gold and agent theorem statements into abstracted entailment goals (the agent's implementation replaced by a variable), tries a fixed tactic sweep and kernel-checked countermodels, and prints one JSON line per goal. -/
import Mathlib

open Lean Meta Elab Term Command

namespace VB117

/-- Configuration passed by the driver as a JSON string. -/
structure Config where
  item : String
  mode : String                       -- "agent" or "control"
  controls : Array String := #[]      -- control mode: subset of C1..C7
  prove : Bool := true                -- run the tactic sweep (false = elaboration only)
  refute : Bool := true               -- run the countermodel search
  goldNs : String := "VB117Gold"
  candNs : String := "VB117Cand"
  hbTac : Nat := 40000                -- heartbeat budget per tactic attempt (option units, x1000 internally)
  hbHyp : Nat := 10000                -- heartbeat budget per countermodel hypothesis/decide attempt
  maxCombos : Nat := 64               -- counterexample inputs tried per countermodel
  maxCands : Nat := 8                 -- countermodels tried per goal
  mapVersion : String := "v1"         -- "v1" (phase 0) or "v2" (instantiate implicit/instance binders, fill optional args, role-matched)
  exportPrompts : Bool := false       -- emit the full pretty-printed goal for tier T1 prompts
  proofsFile : String := ""           -- tier T1: JSON {"kind:goal": [proof text, ...]} checked against the exact goal term
  hbT1 : Nat := 100000                -- heartbeat budget per T1 proof check
  deriving FromJson, ToJson, Inhabited

def emit (j : Json) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn ("VB117JSON " ++ j.compress)
  out.flush

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Names of generated declarations that are not user-written statements or definitions. -/
def auxComponent (s : String) : Bool :=
  s.startsWith "eq_" || s == "induct" || s == "mutual_induct" || s.startsWith "match_" ||
  s.startsWith "proof_" || s.startsWith "_" || s == "fun_cases" || s.endsWith "_def" && s.startsWith "eq" ||
  s == "inj" || s == "injEq" || s == "sizeOf_spec" || s == "ext_iff" || s == "ext" ||
  s == "rec" || s == "recOn" || s == "casesOn" || s == "noConfusion" || s == "noConfusionType" ||
  s == "below" || s == "brecOn" || s == "binductionOn" || s == "ibelow" || s == "mk" ||
  s.startsWith "vb117_out"

def isAuxName (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
  (match n with
   | .str _ s => auxComponent s
   | _ => false)

/-- Declarations added in this file under namespace `ns` (generated auxiliaries excluded), sorted by source
    line when Lean recorded one and by name otherwise, so the order is deterministic. -/
def localDecls (ns : Name) : CoreM (Array ConstantInfo) := do
  let env ← getEnv
  let mut out : Array (Nat × String × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₂.toList do
    if ns.isPrefixOf n && !isAuxName n then
      let line := match ← findDeclarationRanges? n with
        | some r => r.range.pos.line
        | none => 1000000
      out := out.push (line, n.toString, ci)
  let sorted := out.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1))
  return sorted.map (·.2.2)

def isPropValued (ci : ConstantInfo) : MetaM Bool :=
  forallTelescopeReducing ci.type fun _ b => return b.isProp

def isComputationalDef (ci : ConstantInfo) : MetaM Bool := do
  match ci with
  | .defnInfo _ | .opaqueInfo _ =>
    if isInstanceCore (← getEnv) ci.name then return false
    if (← isPropValued ci) then return false
    -- skip `Prop`- and `Sort`-valued things and type definitions
    let isType ← forallTelescopeReducing ci.type fun _ b => return b.isSort
    return !isType
  | _ => return false

/-- Transitive "mentions" relation over constants declared in this file. -/
partial def mentions (targets : NameSet) (n : Name) (cache : IO.Ref (Std.HashMap Name Bool))
    (visiting : NameSet := {}) : CoreM Bool := do
  if targets.contains n then return true
  if let some b := (← cache.get).get? n then return b
  if visiting.contains n then return false
  let env ← getEnv
  -- imported constants cannot mention constants of this file
  if (env.getModuleIdxFor? n).isSome then return false
  let some ci := env.find? n | return false
  let body := match ci with
    | .defnInfo d => some d.value
    | .opaqueInfo d => some d.value
    | _ => none
  let tyConsts := ci.type.getUsedConstants
  let bodyConsts := match body with | some b => b.getUsedConstants | none => #[]
  let mut res := false
  for m in tyConsts ++ bodyConsts do
    if m != n then
      if (← mentions targets m cache (visiting.insert n)) then
        res := true
        break
  cache.modify (·.insert n res)
  return res

/-- Unfold (delta-expand) every constant satisfying `p`, repeatedly, up to `rounds` passes. -/
def unfoldWhere (e : Expr) (p : Name → Bool) (rounds : Nat := 25) : MetaM Expr := do
  let mut e := e
  for _ in [0:rounds] do
    let e' ← Meta.transform e (pre := fun t => do
      match t.getAppFn with
      | .const n _ =>
        if p n then
          if let some t' ← delta? t (fun m => m == n) then
            return .visit t'.headBeta
        return .continue
      | _ => return .continue)
    if e' == e then break
    e := e'
  return e

def betaAll (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => return .done t.headBeta)

def replaceConsts (e : Expr) (m : Std.HashMap Name Expr) : Expr :=
  e.replace fun t => match t with
    | .const n _ => m.get? n
    | _ => none

def ppStr (e : Expr) (n : Nat := 700) : MetaM String := do
  let s := toString (← ppExpr e)
  return if s.length > n then (s.take n) ++ "…" else s

/-! ## Type conversions between gold and agent vocabularies (fixed library) -/

def isResultLike (t : Expr) : Option (Name × Expr) :=
  if t.isAppOfArity ``Option 1 then some (``Option, t.appArg!)
  else if t.isAppOfArity ``Except 2 then some (``Except, t.appArg!)
  else match t.getAppFn with
    | .const n _ =>
      if n == `VeriBench.Result && t.getAppNumArgs == 1 then some (`VeriBench.Result, t.appArg!) else none
    | _ => none

/-- Convert value `x : src` to type `dst`. Returns the term and whether the conversion loses information. -/
partial def convVal (x src dst : Expr) : MetaM (Option (Expr × Bool)) := do
  let src ← whnfR src
  let dst ← whnfR dst
  if ← withNewMCtxDepth (isDefEq src dst) then return some (x, false)
  if src.isConstOf ``Nat && dst.isConstOf ``Int then
    return some (← mkAppM ``Int.ofNat #[x], false)
  if src.isConstOf ``Int && dst.isConstOf ``Nat then
    return some (← mkAppM ``Int.toNat #[x], true)
  if src.isAppOfArity ``List 1 && dst.isAppOfArity ``Array 1 then
    let some (y, l) ← convVal (← mkAppM ``List.toArray #[x]) (← mkAppM ``Array #[src.appArg!]) dst | return none
    return some (y, l)
  if src.isAppOfArity ``Array 1 && dst.isAppOfArity ``List 1 then
    let some (y, l) ← convVal (← mkAppM ``Array.toList #[x]) (← mkAppM ``List #[src.appArg!]) dst | return none
    return some (y, l)
  if src.isAppOfArity ``List 1 && dst.isAppOfArity ``List 1 then
    let a := src.appArg!
    let b := dst.appArg!
    let r ← withLocalDeclD `y a fun y => do
      let some (cy, l) ← convVal y a b | return none
      return some (← mkLambdaFVars #[y] cy, l)
    let some (fn, l) := r | return none
    return some (← mkAppM ``List.map #[fn, x], l)
  match isResultLike src with
  | some (kind, inner) =>
    let some dflt ← (try some <$> mkAppOptM ``Inhabited.default #[dst, none] catch _ => pure none) | return none
    let asOpt ← match kind with
      | ``Option => pure x
      | ``Except => mkAppM ``Except.toOption #[x]
      | _ => mkAppM `VeriBench.Result.toOption #[x]
    let r ← withLocalDeclD `y inner fun y => do
      let some (cy, l) ← convVal y inner dst | return none
      return some (← mkLambdaFVars #[y] cy, l)
    let some (fn, _) := r | return none
    let mapped ← mkAppM ``Option.map #[fn, asOpt]
    return some (← mkAppM ``Option.getD #[mapped, dflt], true)
  | none => return none

/-- A view of agent constant `fa : aTy` as a term of gold type `gTy` (same explicit arity, no implicit binders). -/
def buildView (fa aTy gTy : Expr) : MetaM (Option (Expr × Bool)) := do
  if ← withNewMCtxDepth (isDefEq aTy gTy) then return some (fa, false)
  forallTelescopeReducing gTy fun gxs gRes => do
  forallTelescopeReducing aTy fun axs aRes => do
    if gxs.size != axs.size || gxs.size == 0 then return none
    for x in gxs ++ axs do
      if (← x.fvarId!.getBinderInfo) != .default then return none
    if gRes.hasLooseBVars || aRes.hasLooseBVars then return none
    let mut args : Array Expr := #[]
    let mut lossy := false
    for i in [0:gxs.size] do
      let gt ← inferType gxs[i]!
      let aT ← inferType axs[i]!
      if aT.hasFVar || gt.hasFVar then return none
      let some (c, l) ← convVal gxs[i]! gt aT | return none
      args := args.push c
      lossy := lossy || l
    let app := mkAppN fa args
    if aRes.hasFVar || gRes.hasFVar then return none
    let some (out, l) ← convVal app aRes gRes | return none
    lossy := lossy || l
    let lam ← mkLambdaFVars gxs out
    return some (lam, lossy)

/-- Imperative-twin role from the name (VeriBench files pair `f` with `fImp`). -/
def isImpRole (s : String) : Bool :=
  let n := s.toLower
  n.endsWith "imp" || n.endsWith "impl" || (n.splitOn "imperative").length > 1

/-- Agent view with the agent's implicit and instance binders solved by unification and instance search, and
    trailing explicit arguments that have default values filled with those defaults (map version v2). -/
def buildView2 (fa aTy gTy : Expr) : MetaM (Option (Expr × Bool)) := do
  if ← withNewMCtxDepth (isDefEq aTy gTy) then return some (fa, false)
  forallTelescopeReducing gTy fun gxs gRes => do
    if gxs.size == 0 || gRes.hasLooseBVars then return none
    for x in gxs do
      if (← x.fvarId!.getBinderInfo) != .default then return none
    let (ms, bis, aRes) ← forallMetaTelescopeReducing aTy
    let explicitIdx := (Array.range ms.size).filter fun i => bis[i]! == .default
    if explicitIdx.size < gxs.size then return none
    let mut lossy := false
    for k in [0:gxs.size] do
      let m := ms[explicitIdx[k]!]!
      let gt ← inferType gxs[k]!
      let mTy ← instantiateMVars (← inferType m)
      let mTy := if mTy.isOptParam then mTy.appFn!.appArg! else mTy
      if ← isDefEq mTy gt then
        unless ← isDefEq m gxs[k]! do return none
      else
        let some (c, l) ← convVal gxs[k]! gt (← instantiateMVars mTy) | return none
        unless ← isDefEq m c do return none
        lossy := lossy || l
    for k in [gxs.size:explicitIdx.size] do
      let m := ms[explicitIdx[k]!]!
      let mTy ← instantiateMVars (← inferType m)
      match mTy.getOptParamDefault? with
      | some v => unless ← isDefEq m v do return none
      | none => return none
    for i in [0:ms.size] do
      if bis[i]! == .instImplicit then
        let m := ms[i]!
        unless ← m.mvarId!.isAssigned do
          let ty ← instantiateMVars (← inferType m)
          match ← (try some <$> synthInstance ty catch _ => pure none) with
          | some inst => unless ← isDefEq m inst do return none
          | none => return none
    let app ← instantiateMVars (mkAppN fa ms)
    if app.hasExprMVar then return none
    let aRes ← instantiateMVars aRes
    if aRes.hasExprMVar then return none
    let some (out, l) ← convVal app aRes gRes | return none
    let lam ← mkLambdaFVars gxs out
    return some (lam, lossy || l)

/-- Name core for matching (v2): lowercase alphanumerics, leading `my` and trailing role words removed. -/
def normCore (s : String) : String := Id.run do
  let mut t := String.mk (s.toLower.toList.filter Char.isAlphanum)
  if t.startsWith "my" && t.length > 2 then t := t.drop 2
  for suf in ["functional", "func", "imperative", "impl", "imp"] do
    if t.endsWith suf && t.length > suf.length then t := t.dropRight suf.length
  return t

def normName (s : String) : String :=
  let s := s.toLower
  let s := String.mk (s.toList.filter Char.isAlphanum)
  let s := if s.startsWith "my" && s.length > 2 then s.drop 2 else s
  s

/-! ## Tactic attempts and kernel acceptance -/

def withHB {α} (hb : Nat) (x : TermElabM α) : TermElabM α :=
  Core.withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) x

def tryTac (ty : Expr) (tac : TSyntax `tactic) (hb : Nat) : TermElabM (Option Expr) := do
  let s ← saveState
  -- `tryCatchRuntimeEx` also catches heartbeat timeouts, which plain `catch` lets through
  tryCatchRuntimeEx (do
    -- closed goals only: an empty local context keeps outer variables out of the proof
    let mv ← withLCtx {} {} (mkFreshExprMVar ty .syntheticOpaque)
    let gs ← withHB hb do
      let gs ← Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic tac))
      Term.synthesizeSyntheticMVarsNoPostponing
      return gs
    if !gs.isEmpty then
      s.restore
      return none
    let pf ← instantiateMVars mv
    if pf.hasExprMVar || pf.hasLevelMVar then
      s.restore
      return none
    return some pf)
    (fun _ => do s.restore; return none)

/-- Add `pf : ty` as a theorem; the kernel checks it. Returns its axioms, or none if rejected. -/
def kernelAccept (declName : Name) (ty pf : Expr) : TermElabM (Option (Array Name)) := do
  let s ← saveState
  tryCatchRuntimeEx (do
    let ty ← instantiateMVars ty
    let pf ← instantiateMVars pf
    let lps := (collectLevelParams (collectLevelParams {} ty) pf).params.toList
    addDecl (.thmDecl { name := declName, levelParams := lps, type := ty, value := pf })
    return some (← collectAxioms declName))
    (fun _ => do s.restore; return none)

def axiomsOk (axs : Array Name) : Bool := axs.all (allowedAxioms.contains ·)

/-- Fixed tactic sweep (tier T0), tried in order. -/
def sweep : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[
    ("intros_assumption", ← `(tactic| (intros; assumption))),
    ("simp_all", ← `(tactic| (intros; simp_all))),
    ("grind", ← `(tactic| (intros; grind))),
    ("aesop", ← `(tactic| (intros; aesop))),
    ("simp_all_omega", ← `(tactic| (intros; simp_all <;> omega))),
    ("exact?", ← `(tactic| (intros; exact?)))]

/-- Tactics for proving a countermodel's hypotheses (concrete function substituted). -/
def hypSweep : TermElabM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| decide), ← `(tactic| simp), ← `(tactic| (intros; simp_all)),
           ← `(tactic| (intros; omega)), ← `(tactic| (intros; grind))]

/-! ## Input pools for counterexample search -/

partial def pool (t : Expr) : MetaM (Array Expr) := do
  let t ← whnfR t
  if t.isConstOf ``Nat then return #[0, 1, 2, 3, 5, 10].map mkNatLit
  if t.isConstOf ``Int then return #[toExpr (0 : Int), toExpr (1 : Int), toExpr (-1 : Int), toExpr (2 : Int), toExpr (-3 : Int)]
  if t.isConstOf ``Bool then return #[toExpr true, toExpr false]
  if t.isConstOf ``Char then return #['a', 'A', '0', ' '].map toExpr
  if t.isConstOf ``String then return #["", "a", "ab", "aB c", "hello world"].map toExpr
  if t.isAppOfArity ``List 1 then
    let a := t.appArg!
    let ps ← pool a
    if ps.size == 0 then return #[← mkAppOptM ``List.nil #[a]]
    let p0 := ps[0]!
    let p1 := ps[1]?.getD p0
    let p2 := ps[2]?.getD p1
    return #[← mkListLit a [], ← mkListLit a [p1], ← mkListLit a [p2, p1], ← mkListLit a [p1, p2, p0], ← mkListLit a [p1, p1]]
  if t.isAppOfArity ``Array 1 then
    let a := t.appArg!
    let ls ← pool (← mkAppM ``List #[a])
    return ← ls.mapM fun l => mkAppM ``List.toArray #[l]
  if t.isAppOfArity ``Option 1 then
    let a := t.appArg!
    let ps ← pool a
    let mut out := #[← mkAppOptM ``Option.none #[a]]
    for p in ps.toList.take 2 do out := out.push (← mkAppM ``Option.some #[p])
    return out
  if t.isAppOfArity ``Prod 2 then
    let a := t.appFn!.appArg!
    let b := t.appArg!
    let pa ← pool a
    let pb ← pool b
    let mut out := #[]
    for x in pa.toList.take 2 do
      for y in pb.toList.take 2 do
        out := out.push (← mkAppM ``Prod.mk #[x, y])
    return out
  try return #[← mkAppOptM ``Inhabited.default #[t, none]] catch _ => return #[]

/-- Cartesian product of pools, capped at `cap` combinations. -/
def combos (pools : Array (Array Expr)) (cap : Nat) : Array (Array Expr) := Id.run do
  let mut acc : Array (Array Expr) := #[#[]]
  for p in pools do
    let mut next := #[]
    for a in acc do
      for v in p do
        if next.size < cap then next := next.push (a.push v)
    acc := next
  return acc

/-! ## Countermodels and refutation -/

/-- Closed argument tuples at which an expression applies `f` to `arity` arguments. -/
partial def collectApps (f : Expr) (arity : Nat) (e : Expr) (acc : Array (Array Expr)) : Array (Array Expr) :=
  let acc := if e.getAppFn == f && e.getAppNumArgs == arity then
      let args := e.getAppArgs
      if args.all (fun a => !a.hasLooseBVars && !a.hasFVar && !a.hasMVar) && !acc.contains args then acc.push args else acc
    else acc
  match e with
  | .app a b => collectApps f arity b (collectApps f arity a acc)
  | .lam _ t b _ => collectApps f arity b (collectApps f arity t acc)
  | .forallE _ t b _ => collectApps f arity b (collectApps f arity t acc)
  | .letE _ t v b _ => collectApps f arity b (collectApps f arity v (collectApps f arity t acc))
  | .mdata _ b => collectApps f arity b acc
  | .proj _ _ b => collectApps f arity b acc
  | _ => acc

/-- Closed argument tuples at which the hypotheses apply `f`. -/
def closedCalls (f : Expr) (arity : Nat) (hyps : Array Expr) : Array (Array Expr) :=
  hyps.foldl (fun acc h => collectApps f arity h acc) #[]

/-- Candidate countermodels for abstraction variable `f` (type `fTy`), given the concrete reference `impl`. -/
def candidates (f fTy impl : Expr) (useImpl : Bool) (hyps : Array Expr) (cap : Nat) :
    MetaM (Array (String × Expr)) := do
  forallTelescopeReducing fTy fun xs res => do
    if res.hasFVar then return #[]
    for x in xs do
      if (← x.fvarId!.getBinderInfo) != .default then return #[]
      if (← inferType x).hasFVar then return #[]
    let mut out : Array (String × Expr) := #[]
    if useImpl then out := out.push ("agent_impl", impl)
    let some dflt ← (try some <$> mkAppOptM ``Inhabited.default #[res, none] catch _ => pure none) | return out
    -- lookup table: the reference on the concrete inputs the hypotheses mention, default elsewhere
    let calls := closedCalls f xs.size hyps
    if calls.size > 0 && xs.size > 0 then
      try
        let mut body := dflt
        for t in calls.reverse do
          let mut cond : Option Expr := none
          for i in [0:xs.size] do
            let eq ← mkEq xs[i]! t[i]!
            cond := some (match cond with | none => eq | some c => mkAnd c eq)
          let some c := cond | continue
          body ← mkAppM ``ite #[c, mkAppN impl t, body]
        out := out.push ("table", ← mkLambdaFVars xs body)
      catch _ => pure ()
    -- constants
    let ps ← pool res
    let mut consts : Array Expr := #[dflt]
    for p in ps.toList.take 3 do
      if !(← consts.anyM fun c => withNewMCtxDepth (isDefEq c p)) then consts := consts.push p
    let mut k := 0
    for c in consts do
      out := out.push (s!"const_{k}", ← mkLambdaFVars xs c)
      k := k + 1
    -- projections
    for i in [0:xs.size] do
      if ← withNewMCtxDepth (isDefEq (← inferType xs[i]!) res) then
        out := out.push (s!"proj_{i}", ← mkLambdaFVars xs xs[i]!)
    return out.toList.take cap |>.toArray

/-- Try to prove `¬ G` by a concrete counterexample input found by kernel-checked `decide`. -/
def refuteByInput (G : Expr) (cfg : Config) : TermElabM (Option Expr) := do
  forallTelescope G fun xs body => do
    -- data binders get pool values; Prop binders must be decided true
    let mut pools : Array (Array Expr) := #[]
    let mut dataIdx : Array Nat := #[]
    for i in [0:xs.size] do
      let ty ← inferType xs[i]!
      if !(← isProp ty) then
        if ty.hasFVar then return none
        let p ← pool ty
        if p.isEmpty then return none
        pools := pools.push p
        dataIdx := dataIdx.push i
    let decideTac ← `(tactic| decide)
    for combo in combos pools cfg.maxCombos do
      let s ← saveState
      let mut args : Array Expr := #[]
      let mut ok := true
      let mut d := 0
      for i in [0:xs.size] do
        let ty := (← inferType xs[i]!).replaceFVars (xs.extract 0 i) args
        if dataIdx.contains i then
          args := args.push combo[d]!
          d := d + 1
        else
          match ← tryTac ty decideTac cfg.hbHyp with
          | some pf => args := args.push pf
          | none => ok := false; break
      if !ok then
        s.restore
        continue
      let bodyI := body.replaceFVars xs args
      match ← tryTac (mkNot bodyI) decideTac cfg.hbHyp with
      | some hNot =>
        let r ← withLocalDeclD `hG G fun hG => do
          mkLambdaFVars #[hG] (mkApp hNot (mkAppN hG args))
        return some r
      | none =>
        s.restore
        continue
    return none

/-! ## Goal records -/

structure GoalOut where
  kind : String
  goal : String
  gold : String
  statable : Bool
  agentDependent : Bool
  outcome : String
  method : String := ""
  axioms : Array String := #[]
  nHyps : Nat := 0
  pp : String := ""
  note : String := ""
  ppFull : String := ""
  deriving ToJson

/-- Tier T1: elaborate a proof text (a tactic block) against the exact goal term; kernel and axioms are checked by the caller. -/
def tryProofText (E : Expr) (txt : String) (hb : Nat) : TermElabM (Option Expr) := do
  match Parser.runParserCategory (← getEnv) `term ("by\n" ++ txt) with
  | .error _ => return none
  | .ok stx =>
    let s ← saveState
    tryCatchRuntimeEx (do
      let pf ← withHB hb <| withLCtx {} {} do
        let pf ← Term.withoutErrToSorry <| Term.elabTermEnsuringType stx E
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars pf
      if pf.hasExprMVar || pf.hasLevelMVar then
        s.restore
        return none
      return some pf)
      (fun _ => do s.restore; return none)

def ppFullStr (e : Expr) : MetaM String :=
  withOptions (fun o => ((o.setBool `pp.fullNames true).setBool `pp.deepTerms true).setNat `pp.maxSteps 1000000) do
    return toString (← ppExpr e)

/-- Variables of `G` closed under sharing a variable with a hypothesis; the hypotheses of that component. -/
def component (fs : Array Expr) (hyps : Array Expr) (G : Expr) : Array Nat × Array Expr := Id.run do
  let varsOf (e : Expr) : Array Nat := (Array.range fs.size).filter fun i => e.containsFVar fs[i]!.fvarId!
  let mut vs : Array Nat := varsOf G
  let mut used : Array Bool := hyps.map fun _ => false
  let mut changed := true
  while changed do
    changed := false
    for j in [0:hyps.size] do
      if !used[j]! then
        let hv := varsOf hyps[j]!
        if hv.any (vs.contains ·) then
          used := used.set! j true
          for v in hv do
            if !vs.contains v then vs := vs.push v
          changed := true
  let sorted := vs.qsort (· < ·)
  let hs := (Array.range hyps.size).filterMap fun j => if used[j]! then some hyps[j]! else none
  return (sorted, hs)

/-- Prove or refute `E := ∀ fs, hyps → G`, where only the hypotheses sharing a function variable with `G`
    (transitively) are kept: a proof from fewer hypotheses still proves the full entailment. -/
def decideGoal (cfg : Config) (fsAll : Array Expr) (implsAll : Array Expr) (useImpl : Bool)
    (hypsAll : Array Expr) (G : Expr) (t1 : Array String) (tag : String) (counter : IO.Ref Nat) : TermElabM (String × String × Array String) := do
  let (vs, hyps) := component fsAll hypsAll G
  let fs := vs.map (fsAll[·]!)
  let impls := vs.map (implsAll[·]!)
  let E ← mkForallFVars fs (← hyps.foldrM (fun h acc => mkArrow h acc) G)
  if cfg.prove then
    for (nm, tac) in ← sweep do
      if let some pf ← tryTac E tac cfg.hbTac then
        counter.modify (· + 1)
        let dn := Name.mkSimple s!"vb117_out_{tag}_{← counter.get}"
        if let some axs ← kernelAccept dn E pf then
          if axiomsOk axs then
            return ("proved", nm, axs.map toString)
          -- an accepted proof with a disallowed axiom (sorryAx, ofReduceBool) does not count
    -- tier T1: candidate proof texts from the open prover, checked against this exact goal
    let mut k := 0
    for txt in t1 do
      k := k + 1
      if let some pf ← tryProofText E txt cfg.hbT1 then
        counter.modify (· + 1)
        let dn := Name.mkSimple s!"vb117_out_{tag}_t1_{← counter.get}"
        if let some axs ← kernelAccept dn E pf then
          if axiomsOk axs then
            return ("proved", s!"t1_{k}", axs.map toString)
  if cfg.refute && fs.size > 0 then
    -- target: first abstraction variable occurring in G (else the first one)
    let tIdx := (fs.findIdx? (fun f => G.containsFVar f.fvarId!)).getD 0
    let f := fs[tIdx]!
    let fTy ← inferType f
    let cands ← candidates f fTy impls[tIdx]! useImpl hyps cfg.maxCands
    let hs ← hypSweep
    for (cname, cand) in cands do
      let s ← saveState
      let σ := (impls.set! tIdx cand)
      -- each hypothesis must hold of the countermodel
      let mut hpfs : Array Expr := #[]
      let mut ok := true
      for h in hyps do
        let hI ← betaAll (h.replaceFVars fs σ)
        let mut got : Option Expr := none
        for tac in hs do
          if got.isNone then got ← tryTac hI tac cfg.hbHyp
        match got with
        | some p => hpfs := hpfs.push p
        | none => ok := false; break
      if !ok then
        s.restore
        continue
      let GI ← betaAll (G.replaceFVars fs σ)
      match ← refuteByInput GI cfg with
      | none =>
        s.restore
        continue
      | some hNotG =>
        let pfNotE ← withLocalDeclD `hE E fun hE =>
          mkLambdaFVars #[hE] (mkApp hNotG (mkAppN hE (σ ++ hpfs)))
        counter.modify (· + 1)
        let dn := Name.mkSimple s!"vb117_out_{tag}_ref_{← counter.get}"
        match ← kernelAccept dn (mkNot E) pfNotE with
        | some axs =>
          if axiomsOk axs then
            return ("refuted", cname, axs.map toString)
          s.restore
        | none => s.restore
  return ("unknown", "", #[])

/-! ## Transport of statements -/

structure Ctx where
  fs : Array Expr                 -- abstraction variables
  impls : Array Expr              -- concrete reference for each variable (agent impl, or gold impl in controls)
  candMap : Std.HashMap Name Expr -- agent constant ↦ abstraction variable
  goldMap : Std.HashMap Name Expr -- gold constant ↦ view term over abstraction variables
  candTargets : NameSet           -- agent constants being abstracted
  goldTargets : NameSet           -- gold constants being replaced

/-- Transform one statement: unfold this file's `Prop` definitions in the namespace and anything mentioning
    a replaced constant, substitute, and check that no replaced constant leaks back. -/
def transport (ctx : Ctx) (ty : Expr) (ns : Name) (targets : NameSet) (subst : Std.HashMap Name Expr)
    (cache : IO.Ref (Std.HashMap Name Bool)) : TermElabM (Option Expr × String) := do
  let env ← getEnv
  -- which local constants must be unfolded
  let pred : Name → Bool := fun n =>
    !targets.contains n && ns.isPrefixOf n && (env.getModuleIdxFor? n).isNone
  -- unfold Prop-valued local definitions and local definitions mentioning targets
  let mut e := ty
  for _ in [0:25] do
    let used := e.getUsedConstants
    let mut toUnfold : NameSet := {}
    for n in used do
      if pred n then
        let some ci := env.find? n | continue
        match ci with
        | .defnInfo _ =>
          let pv ← isPropValued ci
          if pv || (← mentions targets n cache) then toUnfold := toUnfold.insert n
        | _ => pure ()
    if toUnfold.isEmpty then break
    e ← unfoldWhere e (fun n => toUnfold.contains n) 1
  let e2 := replaceConsts e subst
  let e2 ← betaAll e2
  -- leak check: no replaced constant, and no local constant that mentions one
  for n in e2.getUsedConstants do
    if targets.contains n then return (none, s!"leak:{n}")
    if pred n then
      if (← mentions targets n cache) then return (none, s!"leak_via:{n}")
  -- v2.1: a statement whose type still contains `sorry` did not fully elaborate (error recovery inserted it)
  if e2.hasSorry then return (none, "contains_sorry")
  try
    Meta.check e2
    unless (← isProp e2) do return (none, "not_prop")
  catch ex => return (none, s!"ill_typed:{← ex.toMessageData.toString}")
  return (some e2, "")

/-! ## Main command -/

def runItem (cfg : Config) : TermElabM Unit := do
  let goldNs := cfg.goldNs.toName
  let candNs := cfg.candNs.toName
  let goldDecls ← localDecls goldNs
  let goldObl := goldDecls.filter fun ci => match ci with
    | .thmInfo _ => !((ci.name.toString.splitOn "vb117_ex_").length > 1)
    | _ => false
  let goldExamples := goldDecls.filter fun ci => match ci with
    | .thmInfo _ => (ci.name.toString.splitOn "vb117_ex_").length > 1
    | _ => false
  -- gold interface: computational definitions occurring in gold obligations (after unfolding Prop defs)
  let env ← getEnv
  let goldDefs ← goldDecls.filterM (fun ci => isComputationalDef ci)
  let goldDefNames : NameSet := goldDefs.foldl (fun s ci => s.insert ci.name) {}
  let mut counts : Std.HashMap Name Nat := {}
  for ci in goldObl do
    let unf ← unfoldWhere ci.type (fun n => goldNs.isPrefixOf n && (env.getModuleIdxFor? n).isNone &&
      match env.find? n with | some (.defnInfo _) => !goldDefNames.contains n | _ => false)
    for n in unf.getUsedConstants do
      if goldDefNames.contains n then counts := counts.insert n (counts.getD n 0 + 1)
  let iface := (goldDefs.filter fun ci => counts.contains ci.name).qsort
    (fun a b => counts.getD a.name 0 > counts.getD b.name 0)
  let cache ← IO.mkRef ({} : Std.HashMap Name Bool)
  let counter ← IO.mkRef 0
  let mut proofs : Std.HashMap String (Array String) := {}
  if cfg.proofsFile != "" then
    let raw ← IO.FS.readFile cfg.proofsFile
    match Json.parse raw with
    | .ok (.obj kvs) =>
      for ⟨k, v⟩ in kvs.toArray do
        match fromJson? (α := Array String) v with
        | .ok arr => proofs := proofs.insert k arr
        | .error _ => pure ()
    | _ => pure ()
  -- build abstraction variables and maps
  let mut fsDecls : Array (Name × Expr × Expr) := #[]   -- (agent-or-gold const, type, concrete)
  let mut goldViewsSpec : Array (Name × Name × Expr) := #[] -- (gold const, var const, view builder placeholder)
  let mut mapRecords : Array Json := #[]
  let mut candDefs : Array ConstantInfo := #[]
  if cfg.mode == "agent" then
    candDefs ← (← localDecls candNs).filterM (fun ci => isComputationalDef ci)
  let mut used : NameSet := {}
  -- mapping decisions
  let mut mapping : Array (Name × Name × String) := #[] -- gold, agent, rule
  if cfg.mode == "agent" then
    for g in iface do
      let gName := match g.name with | .str _ s => s | _ => g.name.toString
      let free := candDefs.filter fun c => !used.contains c.name
      let v2 := cfg.mapVersion == "v2"
      let view (c : ConstantInfo) : MetaM (Option (Expr × Bool)) :=
        if v2 then buildView2 (Lean.mkConst c.name (c.levelParams.map mkLevelParam)) c.type g.type
        else buildView (Lean.mkConst c.name (c.levelParams.map mkLevelParam)) c.type g.type
      let nameMatches := free.filter fun c =>
        if v2 then normCore (match c.name with | .str _ s => s | _ => "") == normCore gName &&
                   isImpRole (match c.name with | .str _ s => s | _ => "") == isImpRole gName
        else normName (match c.name with | .str _ s => s | _ => "") == normName gName
      let exactT ← free.filterM fun c => withNewMCtxDepth (isDefEq c.type g.type)
      let convT ← free.filterM fun c => do
        let r ← (try withNewMCtxDepth (view c) catch _ => pure none)
        return r.isSome
      let lastOf (c : ConstantInfo) : String := match c.name with | .str _ s => s | _ => ""
      let roleExact := exactT.filter fun c => isImpRole (lastOf c) == isImpRole gName
      let roleConv := convT.filter fun c => isImpRole (lastOf c) == isImpRole gName
      let exactR := if v2 then roleExact else exactT
      let convR := if v2 then roleConv else convT
      let pick : Option (ConstantInfo × String) :=
        if v2 then
          if let some c := nameMatches.find? (fun c => exactT.any (·.name == c.name)) then some (c, "v2:name+exact_type")
          else if let some c := nameMatches.find? (fun c => convT.any (·.name == c.name)) then some (c, "v2:name+converted_type")
          else if exactR.size == 1 then some (exactR[0]!, "v2:role+unique_exact_type")
          else if convR.size == 1 then some (convR[0]!, "v2:role+unique_converted_type")
          else none
        else
        if let some c := nameMatches.find? (fun c => exactT.any (·.name == c.name)) then some (c, "name+exact_type")
        else if let some c := nameMatches.find? (fun c => convT.any (·.name == c.name)) then some (c, "name+converted_type")
        else if roleExact.size == 1 then some (roleExact[0]!, "role+exact_type")
        else if exactT.size == 1 then some (exactT[0]!, "unique_exact_type")
        else if roleConv.size == 1 then some (roleConv[0]!, "role+converted_type")
        else if convT.size == 1 then some (convT[0]!, "unique_converted_type")
        else none
      match pick with
      | some (c, rule) =>
        used := used.insert c.name
        mapping := mapping.push (g.name, c.name, rule)
      | none =>
        mapRecords := mapRecords.push (Json.mkObj [("gold", toJson g.name.toString), ("agent", Json.null),
          ("rule", toJson s!"unmapped(name_matches={nameMatches.size},exact={exactT.size},converted={convT.size})")])
  else
    for g in iface do
      mapping := mapping.push (g.name, g.name, "identity_control")
  -- abstraction variables: one per distinct target constant
  let targetsAgent : Array Name := mapping.foldl (fun acc (_, a, _) => if acc.contains a then acc else acc.push a) #[]
  let typesOf ← targetsAgent.mapM fun n => do return (← getConstInfo n).type
  let varNames := targetsAgent.mapIdx fun i _ => Name.mkSimple s!"f{i}"
  let decls : Array (Name × (Array Expr → TermElabM Expr)) := varNames.mapIdx fun i nm => (nm, fun _ => pure typesOf[i]!)
  withLocalDeclsD decls fun fs => do
    let impls := targetsAgent.map fun n => Lean.mkConst n ((env.find? n).get!.levelParams.map mkLevelParam)
    let mut candMap : Std.HashMap Name Expr := {}
    for i in [0:targetsAgent.size] do candMap := candMap.insert targetsAgent[i]! fs[i]!
    let mut goldMap : Std.HashMap Name Expr := {}
    let mut lossyAny := false
    let mut mapOut := mapRecords
    for (g, a, rule) in mapping do
      let i := (targetsAgent.findIdx? (· == a)).get!
      let gTy := (← getConstInfo g).type
      match ← (try (if cfg.mapVersion == "v2" then buildView2 fs[i]! typesOf[i]! gTy else buildView fs[i]! typesOf[i]! gTy) catch _ => pure none) with
      | some (view, lossy) =>
        goldMap := goldMap.insert g view
        lossyAny := lossyAny || lossy
        mapOut := mapOut.push (Json.mkObj [("gold", toJson g.toString), ("agent", toJson a.toString),
          ("rule", toJson rule), ("lossy", toJson lossy)])
      | none =>
        mapOut := mapOut.push (Json.mkObj [("gold", toJson g.toString), ("agent", toJson a.toString),
          ("rule", toJson s!"{rule}:view_failed")])
    let ctx : Ctx := { fs, impls, candMap, goldMap,
                       candTargets := targetsAgent.foldl (·.insert ·) {},
                       goldTargets := mapping.foldl (fun s (g, _, _) => s.insert g) {} }
    let goldTargets : NameSet := goldMap.fold (fun s k _ => s.insert k) {}
    -- transport gold obligations
    let mut goldT : Array (ConstantInfo × Option Expr × String) := #[]
    for ci in goldObl do
      let (e?, why) ← transport ctx ci.type goldNs goldTargets goldMap cache
      goldT := goldT.push (ci, e?, why)
    let mut exT : Array (Option Expr) := #[]
    for ci in goldExamples do
      let (e?, _) ← transport ctx ci.type goldNs goldTargets goldMap cache
      exT := exT.push e?
    emit (Json.mkObj [("item", toJson cfg.item), ("record", toJson "item"), ("mode", toJson cfg.mode),
      ("n_gold_obligations", toJson goldObl.size), ("n_gold_examples", toJson goldExamples.size),
      ("n_iface", toJson iface.size), ("n_vars", toJson fs.size), ("map", Json.arr mapOut),
      ("lossy_map", toJson lossyAny)])
    let depOf (e : Expr) : Bool := fs.any fun f => e.containsFVar f.fvarId!
    let emitGoal (kind : String) (ci : ConstantInfo) (e? : Option Expr) (why : String)
        (hyps : Array Expr) (useImpl : Bool) : TermElabM Unit := do
      match e? with
      | none =>
        emit (toJson ({ kind, goal := ci.name.toString, gold := ci.name.toString, statable := false,
                        agentDependent := false, outcome := "unstatable", note := why } : GoalOut))
      | some G =>
        if !depOf G then
          emit (toJson ({ kind, goal := ci.name.toString, gold := ci.name.toString, statable := true,
                          agentDependent := false, outcome := "agent_independent", pp := ← ppStr G } : GoalOut))
        else
          let tag := kind.replace "-" "_"
          let st ← saveState
          let t1 := proofs.getD s!"{kind}:{ci.name}" #[]
          let (out, meth, axs) ← tryCatchRuntimeEx (decideGoal cfg fs impls useImpl hyps G t1 tag counter)
            (fun _ => do st.restore; return ("unknown", "runtime_exception", #[]))
          let full ← if cfg.exportPrompts && out == "unknown" then do
              let (vs, hs) := component fs hyps G
              let E ← mkForallFVars (vs.map (fs[·]!)) (← hs.foldrM (fun h acc => mkArrow h acc) G)
              ppFullStr E
            else pure ""
          emit (toJson ({ kind, goal := ci.name.toString, gold := ci.name.toString, statable := true,
                          agentDependent := true, outcome := out, method := meth,
                          axioms := axs, nHyps := hyps.size, pp := ← ppStr G, ppFull := full } : GoalOut))
    if cfg.mode == "agent" then
      -- agent statements
      let candThms := (← localDecls candNs).filter (·.isThm)
      let candTargets : NameSet := targetsAgent.foldl (·.insert ·) {}
      let mut hyps : Array Expr := #[]
      let mut dropped : Array Json := #[]
      for ci in candThms do
        let (e?, why) ← transport ctx ci.type candNs candTargets candMap cache
        match e? with
        | some e => if depOf e then hyps := hyps.push e
                    else dropped := dropped.push (Json.mkObj [("thm", toJson ci.name.toString), ("why", toJson "no_variable")])
        | none => dropped := dropped.push (Json.mkObj [("thm", toJson ci.name.toString), ("why", toJson why)])
      emit (Json.mkObj [("item", toJson cfg.item), ("record", toJson "agent_statements"),
        ("n_agent_theorems", toJson candThms.size), ("n_hyps", toJson hyps.size), ("dropped", Json.arr dropped)])
      -- vacuity
      if hyps.size > 0 && cfg.prove then
        let V ← mkForallFVars fs (← hyps.foldrM (fun h acc => mkArrow h acc) (mkConst ``False))
        let mut vac := false
        for (_, tac) in ← sweep do
          if !vac then
            if let some pf ← tryTac V tac cfg.hbTac then
              counter.modify (· + 1)
              if let some axs ← kernelAccept (Name.mkSimple s!"vb117_out_vac_{← counter.get}") V pf then
                if axiomsOk axs then vac := true
        emit (Json.mkObj [("item", toJson cfg.item), ("record", toJson "vacuity"), ("vacuous", toJson vac)])
      for (ci, e?, why) in goldT do
        emitGoal "coverage" ci e? why hyps true
    else
      -- controls
      let obls : Array Expr := goldT.filterMap fun (_, e?, _) => e?
      let oblsDep := obls.filter depOf
      let exs := (exT.filterMap id).filter depOf
      for c in cfg.controls do
        match c with
        | "C1" => for (ci, e?, why) in goldT do emitGoal "C1" ci e? why oblsDep false
        | "C2" => for (ci, e?, why) in goldT do emitGoal "C2" ci e? why (oblsDep ++ exs) false
        | "C3" =>
          -- paraphrase: split conjunction bodies and swap the first two independent binders
          let mut para : Array Expr := #[]
          for h in oblsDep do
            let h' ← forallTelescope h fun xs body => do
              if xs.size ≥ 2 then
                let t1 ← inferType xs[1]!
                if !t1.containsFVar xs[0]!.fvarId! then
                  return some (← mkForallFVars #[xs[1]!, xs[0]!] (← mkForallFVars (xs.extract 2 xs.size) body))
              return none
            para := para.push (h'.getD h)
          let mut split : Array Expr := #[]
          for h in para do
            let parts ← forallTelescope h fun xs body => do
              if body.isAppOfArity ``And 2 then
                return some #[← mkForallFVars xs body.appFn!.appArg!, ← mkForallFVars xs body.appArg!]
              return none
            split := split ++ (parts.getD #[h])
          for (ci, e?, why) in goldT do emitGoal "C3" ci e? why split false
        | "C4" =>
          for (ci, e?, why) in goldT do
            let others := (goldT.filter fun (cj, _, _) => cj.name != ci.name).filterMap (fun (_, e?, _) => e?) |>.filter depOf
            emitGoal "C4" ci e? why others false
        | "C5" => for (ci, e?, why) in goldT do emitGoal "C5" ci e? why #[] false
        | "C6" => for (ci, e?, why) in goldT do emitGoal "C6" ci e? why exs false
        | "C7" =>
          -- each obligation instantiated at its first pool input (concrete-instance weakening)
          let mut inst : Array Expr := #[]
          for h in oblsDep do
            let r ← forallTelescope h fun xs body => do
              let mut args : Array Expr := #[]
              for x in xs do
                let ty := (← inferType x).replaceFVars (xs.extract 0 args.size) args
                if ← isProp ty then
                  -- keep hypotheses as implications
                  return none
                let p ← pool ty
                if p.isEmpty then return none
                args := args.push p[0]!
              return some (body.replaceFVars xs args)
            if let some r := r then inst := inst.push r
          for (ci, e?, why) in goldT do emitGoal "C7" ci e? why inst false
        | _ => pure ()
    return ()

elab "#vb117_run " s:str : command => do
  match Json.parse s.getString >>= fromJson? (α := Config) with
  | .error e => logError m!"vb117: bad config: {e}"
  | .ok cfg =>
    liftTermElabM do
      tryCatchRuntimeEx (runItem cfg) fun ex => do
        emit (Json.mkObj [("item", toJson cfg.item), ("record", toJson "crash"),
          ("error", toJson (← ex.toMessageData.toString))])
    emit (Json.mkObj [("item", toJson cfg.item), ("record", toJson "done")])

end VB117
