/- TLDR: Deterministic statement-only context exporter. Reads the namespace-wrapped `Gold.`/`Agent.`
   declarations from the environment, inlines every proposition-valued helper and nullary constant,
   abstracts every function implementation into a universally quantified variable, matches the two
   interfaces by exact type, and emits a proof-free `Context` source plus a per-declaration receipt.
   It never reads a proof term and never emits one. -/
import Mathlib
import Lean

open Lean Elab Command Term Meta

namespace VB169

structure DeclRec where
  name : String
  side : String
  kind : String
  role : String
  typePP : String
  deriving ToJson, Inhabited

structure SlotRec where
  index : Nat
  binder : String
  typePP : String
  gold : String
  agent : String
  rule : String
  deriving ToJson, Inhabited

/-- An agent definition that could only be matched to a reference definition through a
representation change (an adapter).  Reported as a worklist for a later independent reading; the
exporter never accepts one. -/
structure AdapterCandidate where
  gold : String
  goldType : String
  agent : String
  agentType : String
  sameArity : Bool
  sameResult : Bool
  deriving ToJson, Inhabited

structure Report where
  nonce : String
  ok : Bool
  status : String
  reasons : Array String
  notes : Array String
  decls : Array DeclRec
  goldTheorems : Array String
  agentTheorems : Array String
  skippedDecls : Array String
  slots : Array SlotRec
  unmatchedGold : Array String
  unmatchedAgent : Array String
  residualConstants : Array String
  adapterCandidates : Array AdapterCandidate
  goldArgs : Array String
  agentArgs : Array String
  ppMode : String
  contextSource : String
  deriving ToJson, Inhabited

def blank (nonce : String) : Report := { (default : Report) with nonce }

def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- `Prop`-valued: the type is a (possibly nullary) telescope ending in `Prop`. -/
def resultIsProp (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun _ body => return body == mkSort levelZero

partial def piArity : Expr → Nat
  | .forallE _ _ b _ => 1 + piArity b
  | _ => 0

/-- Compiler- and elaborator-generated companions are not part of the agent's or the task's source. -/
def companionSuffixes : List String :=
  ["eq_def", "eq_1", "eq_2", "eq_3", "eq_4", "eq_5", "eq_6", "eq_7", "eq_8", "eq_9", "eq",
   "injEq", "inj", "induct", "induct_unfolding", "fun_cases", "fun_cases_unfolding",
   "sizeOf_spec", "sizeOf_eq", "noConfusionType", "noConfusion", "below", "brecOn",
   "binductionOn", "ibelow", "casesOn", "recOn", "rec", "toCtorIdx", "ctorIdx", "ofNat",
   "match_1", "unsafe_rec", "unfold", "mk"]

/-- A declaration the elaborator generated beside a user declaration, rather than one the author
wrote.  A companion name such as `Foo.inj` or `f.induct` counts only when its prefix really is a
declaration in this environment, so a hand-written `Namespace.inj` is still kept. -/
def isGenerated (env : Environment) (n : Name) : Bool := Id.run do
  if n.isInternal || n.isInternalDetail then return true
  if isAuxRecursor env n || isNoConfusion env n || isRecCore env n then return true
  if (env.find? n).isNone then return true
  let last := n.components.getLast!.toString
  if companionSuffixes.contains last && (env.find? n.getPrefix).isSome then return true
  return false

inductive Role where
  | thm | propHelper | valueConst | implFn | unsupported (why : String)

def roleName : Role → String
  | .thm => "theorem" | .propHelper => "prop_helper" | .valueConst => "value_const"
  | .implFn => "impl_fn" | .unsupported _ => "unsupported"

def classify (ci : ConstantInfo) : MetaM Role := do
  match ci with
  | .thmInfo _ => return .thm
  | .defnInfo d =>
      if !d.levelParams.isEmpty then return .unsupported "universe-polymorphic definition"
      if ← resultIsProp d.type then return .propHelper
      if piArity d.type == 0 then return .valueConst
      return .implFn
  | .axiomInfo _ => return .unsupported "axiom"
  | .opaqueInfo _ => return .unsupported "opaque"
  | .inductInfo _ => return .unsupported "inductive type"
  | .ctorInfo _ => return .unsupported "constructor"
  | .recInfo _ => return .unsupported "recursor"
  | .quotInfo _ => return .unsupported "quotient primitive"

/-- Replace abstracted implementations by their variables and δ-unfold every other source
definition. Mirrors `AbstractSpec.abstractTaskExpr` (veribench-inf experiment 13). -/
partial def rewrite (unfold repl : Std.HashMap Name Expr) (fuel : Nat) (e : Expr) : MetaM Expr := do
  if fuel == 0 then throwError "abstraction expansion limit reached"
  match e with
  | .const n _ =>
      if let some v := repl[n]? then return v
      if let some v := unfold[n]? then return ← rewrite unfold repl (fuel - 1) v
      return e
  | .app f x =>
      return (mkApp (← rewrite unfold repl (fuel-1) f) (← rewrite unfold repl (fuel-1) x)).headBeta
  | .lam n t b bi =>
      return .lam n (← rewrite unfold repl (fuel-1) t) (← rewrite unfold repl (fuel-1) b) bi
  | .forallE n t b bi =>
      return .forallE n (← rewrite unfold repl (fuel-1) t) (← rewrite unfold repl (fuel-1) b) bi
  | .letE n t v b nd =>
      return .letE n (← rewrite unfold repl (fuel-1) t) (← rewrite unfold repl (fuel-1) v)
        (← rewrite unfold repl (fuel-1) b) nd
  | .mdata d b => return .mdata d (← rewrite unfold repl (fuel-1) b)
  | .proj n i b => return .proj n i (← rewrite unfold repl (fuel-1) b)
  | _ => return e

def ppOpts (explicit : Bool) (o : Options) : Options :=
  let o := o.setBool `pp.fullNames true
  let o := o.setBool `pp.explicit explicit
  let o := o.setBool `pp.universes explicit
  let o := o.setBool `pp.coercions true
  -- Generalized field notation (`x.foo` for a non-structure `x`) does not re-elaborate once the
  -- binder's type is no longer inferable from context, so it is never used in an exported file.
  let o := o.setBool `pp.fieldNotation.generalized false
  o

def ppWith (explicit : Bool) (e : Expr) : MetaM String := do
  let fmt ← withOptions (ppOpts explicit) (do return ← Lean.PrettyPrinter.ppExpr e)
  return (fmt.pretty 100).replace "\n" "\n  "

def conj (xs : List Expr) : Expr :=
  xs.foldr (fun p acc => mkApp2 (mkConst ``And) p acc) (mkConst ``True)

def baseOf (n : Name) : String := n.components.getLast!.toString

def imperative (n : Name) : Bool :=
  ["Imp", "Imperative", "Impl", "_imp", "_imperative"].any (baseOf n).endsWith

/-- A representation adapter declared outside this exporter.  Supplying one is a *reading* of the
two sources, so a declaration must carry its own provenance; the exporter never invents one. -/
structure AdapterPair where
  gold : String
  agent : String
  argMaps : Array String
  resultMap : String
  deriving Inhabited

def parseAdapters (s : String) : Except String (Array AdapterPair) := do
  if s.trim.isEmpty then return #[]
  let j ← Lean.Json.parse s
  let pairs := (j.getObjVal? "pairs").toOption.getD (Json.arr #[])
  let arr ← pairs.getArr?
  arr.mapM fun o => do
    let gold ← (← o.getObjVal? "gold").getStr?
    let agent ← (← o.getObjVal? "agent").getStr?
    let maps ← (← o.getObjVal? "argument_maps").getArr?
    let argMaps ← maps.mapM (·.getStr?)
    let resultMap ← (← o.getObjVal? "result_map").getStr?
    return { gold, agent, argMaps, resultMap }

def elabTermStr (s : String) (expected : Option Expr) : TermElabM Expr := do
  match Lean.Parser.runParserCategory (← getEnv) `term s "<adapter>" with
  | .error e => throwError "adapter term does not parse: {s}\n{e}"
  | .ok stx =>
      let e ← elabTerm stx expected
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e

/-- `fun x₁ … xₙ => resultMap (f (argMap₁ x₁) … (argMapₙ xₙ))`, typed against both signatures. -/
def adaptedTerm (goldTy agentTy f : Expr) (argMaps : Array String) (resultMap : String) :
    TermElabM Expr :=
  forallTelescope goldTy fun gxs gres =>
    forallTelescope agentTy fun ays ares => do
      unless gxs.size == ays.size do
        throwError "declared adapter arity mismatch: {gxs.size} reference arguments, {ays.size} candidate arguments"
      unless gxs.size == argMaps.size do
        throwError "declared adapter needs exactly one argument map per argument"
      if gres.hasLooseBVars || ares.hasLooseBVars then
        throwError "declared adapter does not support dependent result types"
      let mut args : Array Expr := #[]
      for h : i in [0:gxs.size] do
        let src ← inferType gxs[i]!
        let tgt ← inferType ays[i]!
        let m ← elabTermStr argMaps[i]! (some (← mkArrow src tgt))
        args := args.push (mkApp m gxs[i]!).headBeta
      let rm ← elabTermStr resultMap (some (← mkArrow ares gres))
      mkLambdaFVars gxs (mkApp rm (mkAppN f args)).headBeta

structure Slot where
  ty : Expr
  gold : Option Name
  agent : Option Name
  rule : String
  adapter : Option AdapterPair := none
  deriving Inhabited

/-- Match each gold implementation with an agent implementation of exactly the same type. -/
def matchInterfaces (goldImpls agentImpls : Array (Name × Expr)) :
    Array Slot × Array String × Array String := Id.run do
  let mut slots : Array Slot := #[]
  let mut used : Array Name := #[]
  let mut unmatchedGold : Array String := #[]
  for (gn, gty) in goldImpls do
    let sameGold := goldImpls.filter (fun x => x.2 == gty)
    let sameAgent := agentImpls.filter (fun x => x.2 == gty && !used.contains x.1)
    if sameAgent.isEmpty then
      unmatchedGold := unmatchedGold.push
        s!"{gn}: no agent definition has this type; agent interface differs from gold"
      slots := slots.push ⟨gty, some gn, none, "unmatched_gold", none⟩
    else if sameGold.size == 1 && sameAgent.size == 1 then
      used := used.push sameAgent[0]!.1
      slots := slots.push ⟨gty, some gn, some sameAgent[0]!.1, "unique_type", none⟩
    else
      let byName := sameAgent.filter (fun x => baseOf x.1 == baseOf gn)
      if byName.size == 1 then
        used := used.push byName[0]!.1
        slots := slots.push ⟨gty, some gn, some byName[0]!.1, "name_within_type", none⟩
      else
        let goldConv := sameGold.filter (fun x => imperative x.1 == imperative gn)
        let agentConv := sameAgent.filter (fun x => imperative x.1 == imperative gn)
        if goldConv.size == 1 && agentConv.size == 1 then
          used := used.push agentConv[0]!.1
          slots := slots.push ⟨gty, some gn, some agentConv[0]!.1, "functional_imperative_convention", none⟩
        else
          unmatchedGold := unmatchedGold.push
            s!"{gn}: {sameGold.size} gold and {sameAgent.size} agent definitions share this type; no unique name or functional/imperative match"
          slots := slots.push ⟨gty, some gn, none, "ambiguous", none⟩
  let mut unmatchedAgent : Array String := #[]
  for (an, aty) in agentImpls do
    if !used.contains an then
      unmatchedAgent := unmatchedAgent.push an.toString
      slots := slots.push ⟨aty, none, some an, "agent_only", none⟩
  return (slots, unmatchedGold, unmatchedAgent)

partial def withSlots (slots : Array Slot) (i : Nat) (acc : Array Expr)
    (k : Array Expr → TermElabM Report) : TermElabM Report := do
  if h : i < slots.size then
    withLocalDeclD (Name.mkSimple ("f" ++ toString i)) slots[i].ty fun v =>
      withSlots slots (i+1) (acc.push v) k
  else k acc

def renderContext (header : String) (binders agentPP goldPP : String) (n : Nat) : String :=
  let args := String.intercalate " " ((List.range n).map (fun i => "f" ++ toString i))
  let app := if n == 0 then "" else " " ++ args
  let all := if n == 0 then "" else "∀ " ++ binders ++ ", "
  let ex := if n == 0 then "" else "∃ " ++ binders ++ ", "
  header ++ "import Mathlib\n\nnamespace Natural\n\n" ++
  "/-- Every statement the agent's own file proves about its implementation. -/\n" ++
  "def AgentSpec " ++ binders ++ " : Prop :=\n  " ++ agentPP ++ "\n\n" ++
  "/-- Every statement the reference task file requires of an implementation. -/\n" ++
  "def GoldSpec " ++ binders ++ " : Prop :=\n  " ++ goldPP ++ "\n\n" ++
  "/-- Formal specification coverage: the agent specification implies every reference obligation. -/\n" ++
  "def Coverage : Prop := " ++ all ++ "AgentSpec" ++ app ++ " → GoldSpec" ++ app ++ "\n\n" ++
  "/-- Non-vacuity: the agent specification is satisfiable. -/\n" ++
  "def Nonvacuous : Prop := " ++ ex ++ "AgentSpec" ++ app ++ "\n\n" ++
  "/-- Leakage control: the reference obligations must NOT hold for an arbitrary implementation. -/\n" ++
  "def LeakGoldOnly : Prop := " ++ all ++ "GoldSpec" ++ app ++ "\n\n" ++
  "/-- Vacuity controls. -/\n" ++
  "def VacuousCoverage : Prop := " ++ all ++ "False → GoldSpec" ++ app ++ "\n\n" ++
  "def VacuousWitness : Prop := " ++ ex ++ "False\n\n" ++
  "end Natural\n"


/-- Everything the exporter derives from one (reference, candidate) pair, with the abstraction
variables still in scope so the caller can either print it or compare it to an exported file. -/
structure Abstraction where
  slots : Array Slot
  vars : Array Expr
  goldBody : Expr
  agentBody : Expr
  goldThms : Array Name
  agentThms : Array Name
  decls : Array DeclRec
  reasons : Array String
  notes : Array String
  skipped : Array String
  unmatchedGold : Array String
  unmatchedAgent : Array String
  adapters : Array AdapterCandidate
  residual : List Name

/-- Derive the abstraction and run `k` with the slot variables in scope. -/
def withAbstraction (adapterJson : String) (k : Abstraction → TermElabM Report) :
    TermElabM Report := do
  let env ← getEnv
  let mut cands : Array (Name × String × ConstantInfo) := #[]
  let mut skipped : Array String := #[]
  let mut genUnfold : Std.HashMap Name Expr := {}
  for (n, ci) in env.constants.toList do
    let s := n.toString
    let side :=
      if s.startsWith "Gold." then "gold"
      else if s.startsWith "Agent." then "agent"
      else if s.startsWith "_private." && (s.splitOn ".Gold.").length > 1 then "gold-private"
      else if s.startsWith "_private." && (s.splitOn ".Agent.").length > 1 then "agent-private"
      else ""
    if side == "" then continue
    if side.endsWith "private" then skipped := skipped.push (s ++ " [private]"); continue
    if isGenerated env n then
      skipped := skipped.push (s ++ " [generated]")
      match ci with
      | .defnInfo d => if d.levelParams.isEmpty then genUnfold := genUnfold.insert n d.value
      | .thmInfo d => if d.levelParams.isEmpty then genUnfold := genUnfold.insert n d.value
      | _ => pure ()
      continue
    cands := cands.push (n, side, ci)
  -- Declaration order follows the original source position, so the exported conjunctions read in
  -- the same order as the files they came from; name order breaks ties.
  let mut keyed : Array (Nat × Nat × String × (Name × String × ConstantInfo)) := #[]
  for c in cands do
    let pos ← match ← findDeclarationRanges? c.1 with
      | some r => pure (r.range.pos.line, r.range.pos.column)
      | none => pure (1000000, 0)
    keyed := keyed.push (pos.1, pos.2, c.1.toString, c)
  keyed := keyed.qsort (fun a b =>
    if a.1 != b.1 then a.1 < b.1 else if a.2.1 != b.2.1 then a.2.1 < b.2.1 else a.2.2.1 < b.2.2.1)
  cands := keyed.map (fun x => x.2.2.2)
  let mut decls : Array DeclRec := #[]
  let mut reasons : Array String := #[]
  let mut goldThms : Array Name := #[]
  let mut agentThms : Array Name := #[]
  let mut unfoldMap : Std.HashMap Name Expr := {}
  let mut goldImpls : Array (Name × Expr) := #[]
  let mut agentImpls : Array (Name × Expr) := #[]
  for (n, side, ci) in cands do
    let role ← classify ci
    decls := decls.push ⟨n.toString, side, kindName ci, roleName role, ← ppWith false ci.type⟩
    match role with
    | .thm => if side == "gold" then goldThms := goldThms.push n else agentThms := agentThms.push n
    | .propHelper | .valueConst =>
        match ci with
        | .defnInfo d => unfoldMap := unfoldMap.insert n d.value
        | _ => pure ()
    | .implFn =>
        if side == "gold" then goldImpls := goldImpls.push (n, ci.type)
        else agentImpls := agentImpls.push (n, ci.type)
    | .unsupported why => reasons := reasons.push s!"unsupported source declaration {n}: {why}"
  -- Declared representation adapters, if any, are consumed before mechanical type matching.
  let declared ← match parseAdapters adapterJson with
    | .error e => throwError "adapter declaration is not readable: {e}"
    | .ok v => pure v
  let mut declaredSlots : Array Slot := #[]
  let mut takenGold : Array Name := #[]
  let mut takenAgent : Array Name := #[]
  for pair in declared do
    let gn := pair.gold.toName
    let an := pair.agent.toName
    let some (_, gty) := goldImpls.find? (fun x => x.1 == gn)
      | throwError "declared adapter names {gn}, which is not a reference implementation here"
    let some (_, aty) := agentImpls.find? (fun x => x.1 == an)
      | throwError "declared adapter names {an}, which is not a candidate implementation here"
    let _ := gty
    takenGold := takenGold.push gn
    takenAgent := takenAgent.push an
    declaredSlots := declaredSlots.push ⟨aty, some gn, some an, "declared_adapter", some pair⟩
  let freeGold := goldImpls.filter (fun x => !takenGold.contains x.1)
  let freeAgent := agentImpls.filter (fun x => !takenAgent.contains x.1)
  let (matched, unmatchedGold, unmatchedAgent) := matchInterfaces freeGold freeAgent
  let slots := declaredSlots ++ matched
  -- Worklist for the later funded mapping step: candidate definitions of the same shape that would
  -- need a representation adapter, which is a reading and never a mechanical match.
  let mut adapters : Array AdapterCandidate := #[]
  for s in slots do
    if s.rule == "unmatched_gold" || s.rule == "ambiguous" then
      if let some gn := s.gold then
        let gRes ← forallTelescope s.ty fun _ b => ppWith false b
        for (an, aty) in agentImpls do
          let aRes ← forallTelescope aty fun _ b => ppWith false b
          adapters := adapters.push ⟨gn.toString, ← ppWith false s.ty, an.toString,
            ← ppWith false aty, piArity s.ty == piArity aty, gRes == aRes⟩
  withSlots slots 0 #[] fun vars => do
    let mut repl : Std.HashMap Name Expr := {}
    for h : i in [0:slots.size] do
      let slot := slots[i]!
      if let some a := slot.agent then repl := repl.insert a vars[i]!
      if let some g := slot.gold then
        match slot.adapter with
        | none => repl := repl.insert g vars[i]!
        | some pair =>
            let some ci := (← getEnv).find? g | throwError "missing {g}"
            repl := repl.insert g
              (← adaptedTerm ci.type slot.ty vars[i]! pair.argMaps pair.resultMap)
    let abstractOf (n : Name) : TermElabM Expr := do
      let some ci := (← getEnv).find? n | throwError "missing {n}"
      rewrite unfoldMap repl 8192 ci.type
    let sourceConsts (a b : Expr) : List Name :=
      ((a.foldConsts (b.foldConsts [] (· :: ·)) (· :: ·)).filter
        (fun n => n.toString.startsWith "Gold." || n.toString.startsWith "Agent.")).eraseDups
    let mut goldBody := conj (← goldThms.toList.mapM abstractOf)
    let mut agentBody := conj (← agentThms.toList.mapM abstractOf)
    let mut residual := sourceConsts goldBody agentBody
    let mut notes : Array String := #[]
    if !residual.isEmpty then
      -- Elaborator-generated companions (`_proof_n`, equation lemmas) can appear inside a
      -- statement; unfold them too rather than leaving a source name in the exported file.
      let wider := genUnfold.fold (fun m k v => m.insert k v) unfoldMap
      let abstractWide (n : Name) : TermElabM Expr := do
        let some ci := (← getEnv).find? n | throwError "missing {n}"
        rewrite wider repl 8192 ci.type
      let g2 ← (try some <$> conj <$> goldThms.toList.mapM abstractWide catch _ => pure none)
      let a2 ← (try some <$> conj <$> agentThms.toList.mapM abstractWide catch _ => pure none)
      match g2, a2 with
      | some g, some a =>
          let r2 := sourceConsts g a
          if r2.length < residual.length then
            goldBody := g; agentBody := a; residual := r2
            notes := notes.push
              "elaborator-generated companion constants were unfolded to clear the statement"
      | _, _ => pure ()
    k { slots, vars, goldBody, agentBody, goldThms, agentThms, decls, reasons, notes, skipped,
        unmatchedGold, unmatchedAgent, adapters, residual }

def buildReport (nonce header adapterJson : String) (explicit : Bool) : TermElabM Report :=
  withAbstraction adapterJson fun a => do
    let mut slotRecs : Array SlotRec := #[]
    let mut binderSrc : Array String := #[]
    let mut goldArgs : Array String := #[]
    let mut agentArgs : Array String := #[]
    for h : i in [0:a.slots.size] do
      let s := a.slots[i]!
      let tpp ← ppWith explicit s.ty
      slotRecs := slotRecs.push ⟨i, "f" ++ toString i, tpp,
        (s.gold.map (·.toString)).getD "", (s.agent.map (·.toString)).getD "", s.rule⟩
      binderSrc := binderSrc.push s!"(f{i} : {tpp})"
      let pick (p q : Option Name) : String :=
        match p.orElse (fun _ => q) with | some x => "@" ++ x.toString | none => "sorry"
      goldArgs := goldArgs.push (pick s.gold s.agent)
      agentArgs := agentArgs.push (pick s.agent s.gold)
    let mut reasons := a.reasons
    if a.goldThms.isEmpty then reasons := reasons.push "no public gold theorem survived filtering"
    if a.agentThms.isEmpty then reasons := reasons.push "no public agent theorem survived filtering"
    if !a.residual.isEmpty then
      reasons := reasons.push s!"source constants survive abstraction: {a.residual}"
    for u in a.unmatchedGold do reasons := reasons.push s!"unmatched gold interface: {u}"
    let ok := a.residual.isEmpty && a.unmatchedGold.isEmpty && !a.goldThms.isEmpty
      && !a.agentThms.isEmpty && a.reasons.isEmpty
    let binders := String.intercalate " " binderSrc.toList
    let source := renderContext header binders (← ppWith explicit a.agentBody)
      (← ppWith explicit a.goldBody) a.slots.size
    return { blank nonce with
      ok, status := if ok then "emitted" else "unresolved", reasons, notes := a.notes,
      decls := a.decls,
      goldTheorems := a.goldThms.map (·.toString), agentTheorems := a.agentThms.map (·.toString),
      skippedDecls := a.skipped, slots := slotRecs, unmatchedGold := a.unmatchedGold,
      unmatchedAgent := a.unmatchedAgent,
      residualConstants := (a.residual.map (·.toString)).toArray, adapterCandidates := a.adapters,
      goldArgs, agentArgs, ppMode := if explicit then "explicit" else "implicit",
      contextSource := source }

/-- Compare the exported `Natural.AgentSpec` / `Natural.GoldSpec` with a freshly derived
abstraction of the same two sources.  This is the pretty-print round trip: it fails if the exported
file elaborates to anything other than the expression the exporter actually built. -/
def roundTrip (nonce adapterJson : String) : TermElabM Report :=
  withAbstraction adapterJson fun a => do
    let env ← getEnv
    let valueOf (n : Name) : TermElabM (Option Expr) := do
      match env.find? n with
      | some (.defnInfo d) => return some d.value
      | _ => return none
    let some agentDef ← valueOf `Natural.AgentSpec | throwError "Natural.AgentSpec is missing"
    let some goldDef ← valueOf `Natural.GoldSpec | throwError "Natural.GoldSpec is missing"
    let agentLam ← mkLambdaFVars a.vars a.agentBody
    let goldLam ← mkLambdaFVars a.vars a.goldBody
    let agentExact := agentDef == agentLam
    let goldExact := goldDef == goldLam
    let agentDefEq ← (try isDefEq agentDef agentLam catch _ => pure false)
    let goldDefEq ← (try isDefEq goldDef goldLam catch _ => pure false)
    let ok := agentExact && goldExact
    let mut reasons : Array String := #[]
    if !agentExact then
      reasons := reasons.push s!"exported AgentSpec differs from the derived abstraction (defeq={agentDefEq})"
    if !goldExact then
      reasons := reasons.push s!"exported GoldSpec differs from the derived abstraction (defeq={goldDefEq})"
    return { blank nonce with
      ok, status := if ok then "roundtrip_exact" else "roundtrip_mismatch", reasons,
      goldTheorems := a.goldThms.map (·.toString), agentTheorems := a.agentThms.map (·.toString),
      notes := a.notes,
      ppMode := s!"agentExact={agentExact} goldExact={goldExact} agentDefEq={agentDefEq} goldDefEq={goldDefEq}" }

end VB169

open VB169 in
/-- `#vb169_extract "<nonce>" "<header comment>" "<adapter declaration JSON>" "<implicit|explicit>"` —
derive the statement-only context.  An empty adapter string means purely mechanical interface
matching; `explicit` prints every implicit and instance argument, which round-trips through the
file in cases where the readable form does not. -/
elab "#vb169_extract " nonceStx:str headerStx:str adapterStx:str modeStx:str : command => do
  let r ← liftTermElabM
    (buildReport nonceStx.getString headerStx.getString adapterStx.getString
      (modeStx.getString == "explicit"))
  logInfo m!"VB169_EXTRACT_JSON {(toJson r).compress}"

open VB169 in
/-- `#vb169_roundtrip "<nonce>" "<adapter declaration JSON>"` — check the exported context against
a freshly derived abstraction of the same sources. -/
elab "#vb169_roundtrip " nonceStx:str adapterStx:str : command => do
  let r ← liftTermElabM (roundTrip nonceStx.getString adapterStx.getString)
  logInfo m!"VB169_ROUNDTRIP_JSON {(toJson r).compress}"
