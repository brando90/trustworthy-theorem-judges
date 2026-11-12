# Experiment 168: is the harsh prover a good detector? P_D and P_F on certified good and bad cases, Tiny-256 (Nov 4, 2026)

**TL;DR.** Brando's handwritten plan (below) treats the harsh prover as a detector of "Agent.FS implies GoldRef.FS" and asks for empirical estimates of P_D (detection) and P_F (false alarm). Verdict as of 11-04-2026: **the existing data are not sufficient to put P_D and P_F in an ML paper**; section 3 says exactly why, section 4 is the plan of good and bad cases, section 5 the budget and funding protocol. Status lines in section 7 are updated as work lands.

Labels: **Lean-checked** = a Lean 4.22.0 / Mathlib compile of the stated file with only `propext`, `Classical.choice`, `Quot.sound`; **reading** = a label assigned by a model or person reading files; **design** = chosen here, before any new result.

## 1. Transcription of the handwritten page (11-04-2026)
`[?]` = my uncertain reading of the handwriting; ~~struck~~ = crossed out on the page. Source: the photo Brando attached to the chat (not stored in Git).

> `Â(y) = H₀` ↓ &nbsp;&nbsp; `Â(y) = H₁` ↓ &nbsp;&nbsp; `ℋ = {H₀, H₁}` &nbsp; (6.437 notation) &nbsp;&nbsp; `𝒴₀ = {y ∈ 𝒴 | Â(y) = H₀}` &nbsp; & &nbsp; `𝒴₁ = {y ∈ 𝒴 | Â(y) = H₁}`
> (rule) **two labels**
> `H₀ = ✓ [text unclear]` &nbsp;&nbsp; `H₁ = ✗ bad [?]`
> `Case ✓ ≜ Prover(x) ≡ Truth(x)` &nbsp;&nbsp; `Case ✗ ≜ Prover(x) ≠ Truth(x)`
> (oval split into 𝒴₀ and 𝒴₁, arrow: "prover detects H₁")
> → "Prob. of detection, if the right thing is right, prob [that the] prover detects H₁" [partly illegible]
> `P_D = Pr[ Â(y) = H₁ | H(y) = H₁ ]` &nbsp; (Sol: this is what 6.437 would define it as.)
> ~~`P_D = Pr[ Prover(y) approves | Truth(y) = correct ]`~~
> ~~`Pr[ Â(y) = H₀ | H(y) = H₀ ]` … (not that interesting; that info is already … [?])~~
> `P_F = probability of false alarm = Pr[ Â(y) = 1 | H(y) = H₀ ]`
> Q: what is a false alarm here? → `Prover(x) ≠ Truth(x)` &nbsp; (brace, arrow to `H₁`)
> **Boxed:** "So we just need empirical experiments to estimate as many cases of those as we can that we can put into the paper! To justify Harsh Prover. Good!"

**Typed restatement** (definitions from 6.437/6.7800 notes, Spring 2024, section 3.1, eq. 3.2 and 3.3: `P_F ≜ P(Ĥ(y)=H₁ | H=H₀)`, `P_D ≜ P(Ĥ(y)=H₁ | H=H₁)`, `P_M = 1 − P_D`; precision depends on the priors, P_D and P_F do not).
- `y` = the pair (Agent.FS, GoldRef.FS) over one shared abstract signature.
- `H₁` = coverage holds: `∀ impl, Agent.FS impl → GoldRef.FS impl` (only this direction; equivalence is not required, Brando 11-04-2026). `H₀` = it fails: `∃ impl, Agent.FS impl ∧ ¬GoldRef.FS impl`.
- `Â(y)=H₁` iff the harsh prover returns a Lean-accepted proof that passes the five conditions of CLAUDE.md "Entailment passes"; otherwise `Â(y)=H₀`.
- **Answer to "what is a false alarm here?"**: the prover credits coverage (`Â=H₁`) when truth is `H₀`. This is the only error that inflates a score. The other half of `Prover(x) ≠ Truth(x)` is a **miss** (`Â=H₀`, truth `H₁`, probability `1 − P_D`), which only undercounts. The two have different consequences, so they are reported separately, not folded into an accuracy.
- The page's `✓/✗` "case" labels are read as the two outcomes of the test (prover agrees / disagrees with truth), not as the hypotheses themselves; the hypotheses are about the truth of the implication. **This is my resolution of an ambiguity in the notes; tell me if you meant otherwise.**
- The struck-out `Pr[Â=H₀ | H=H₀]` is the true-negative rate `1 − P_F`; it carries no new information.
- Why P_D and P_F and not accuracy or precision: the share of good and bad cases in our control suite is a design choice, and accuracy and precision change with it; P_D and P_F do not (6.437 section 3.1).

## 2. What the paper would claim
1. **C1, no inflated credit:** `P_F ≤ α` with a stated confidence bound (the one-sided claim a headline metric needs).
2. **C2, power:** `P_D` with an interval, by case family.
3. **C3, how to read a score:** if the prover credits a share `r` of natural cases, and the control estimates transfer, true coverage is `π = (r − P_F) / (P_D − P_F)` (Rogan-Gladen correction); with `P_F ≈ 0` this is `r / P_D ≥ r`, so a 0.80 means "at least 0.80" and, if `P_D < 1`, probably more. The transfer assumption is the weak point and is testable with the human ratings (section 6).
4. **Operating curve:** P_D against P_F as the proof-search budget grows (6.437 section 3.2 "operating characteristic"; here the knob is the budget ladder, not a likelihood threshold).

## 3. Do we have enough data? No. (Evidence inventory)
Existing evidence, veribench-inf experiment 12 (Gemini 3.1 Pro HIGH and a Lean tactic matrix on 30 references; commit `4f97c875`, results table `tables/controls_per_task.csv`), all Lean-checked:

| Quantity | Observed | Wilson 95% | What it supports |
|---|---|---|---|
| P_D, reordered positives (Gemini HIGH, pooled) | 24/24 | [0.862, 1.000] | recovery of a conjunction reordering only |
| P_D, held-out test positives (Gemini HIGH) | 17/17 | [0.816, 1.000] | same families, 17 distinct references |
| P_F, weakened negatives (Gemini HIGH and tactic union, pooled) | 0/19 | [0.000, 0.168] | one negative family (spec weakened to `f = g`) |
| P_F, held-out test negatives | 0/13 | [0.000, 0.228] | same |
| Adversarial integrity attacks accepted by the repaired fixed-goal checker | 0/7 | [0.000, 0.354] | seven hand-made attacks; the raw saved rule accepted 6 of 7 |

Why this is not sufficient for an ML paper:
1. **Denominators.** 0/19 supports only `P_F ≤ 0.17` (two-sided 95%). To claim `P_F ≤ 0.05` with zero false alarms you need at least 72 certified negatives (exact two-sided; 59 one-sided). 0/7 attacks is a demonstration, not a rate.
2. **Families.** One negative family (equality of the two implementations, which fails for almost any non-trivial gold) and two positive families (reordered, stronger by a free Boolean). No near-miss negatives (an off-by-one bound, a dropped conjunct, a flipped implication, a wrong domain) and no positives that need a real lemma. A prover that never proves anything false and proves every trivial reordering can still fail on every genuine case.
3. **Not the intended prover.** The harsh prover Brando plans to use (Pi + the Anthropic key Vals gave him, high effort) has not been run on any control; only Gemini and tactics were.
4. **Clustering.** The 19 and 24 cases come from at most 26 tasks; the effective sample for P_D and P_F is tasks, so the intervals must be cluster intervals over tasks. Existing controls: 26.
5. **Labels by construction.** Truth is fixed by a compiled certificate (proof for H₁, countermodel for H₀). Cases where no certificate was found are excluded, which favors provable positives; the excluded share must be reported.
6. **No natural population.** Real agent outputs have no ground truth for faithfulness yet. Estimates on constructed cases do not automatically transfer (this is what the human ratings test).
7. **Integrity is a separate error source.** `P_F` of the whole pipeline includes statement-extraction and bridge errors, not only the prover; experiment 12 measured that the raw saved rule credits 6 of 7 invalid controls. The detector must be defined as the repaired pipeline, and its attack suite widened.
8. **No budget ladder, no repeat variance.** Single runs; no operating curve.

## 4. Plan: more good and bad cases (design, fixed before any new result)
**Unit.** One (task, family) case over one shared abstract signature, built as in experiment 12 (`abstract_spec%` over the unchanged gold theorems, implementations replaced by universally quantified functions). **Ground truth** is an independently compiled Lean certificate, never the tested prover's output: H₁ = a proof of `∀ f g, A f g → G f g` plus a satisfiability witness for `A`; H₀ = a proof of `¬ ∀ f g, A f g → G f g` (a countermodel). A case with neither certificate is **ineligible**, listed with its reason, and reported as missingness.

**Tasks.** All Tiny-256 tasks whose gold file compiles and has a unique implementation pair (experiment 12: 26 of the 30 selected). Target at least 60 distinct tasks, a stratum per task set (security, easy, CS, HumanEval, real code), chosen by a fixed hash order before any prover run; the 30 experiment 12 tasks keep their original engineering/test split, new tasks are all held-out test.

**Good cases (H₁), certificate by construction, not by search:**
| Id | Family | Why it matters |
|---|---|---|
| G0 | identity | pipeline control |
| G1 | conjunct reordering | exists in experiment 12 |
| G2 | stronger by an extra constraint | exists; shows direction, not equivalence |
| G3 | conjunct nesting / currying / double negation | logical restructuring a tactic may miss |
| G4 | one gold theorem restated in an equivalent form needing a library lemma (`List.length l = 0` versus `l = []`, `¬ b < a` versus `a ≤ b`, `∀ x ∈ l` versus `all`) | non-trivial deduction |
| G5 | gold properties collapsed into one correctness theorem and the converse organization (Post as one conjunction versus separate property theorems) | how real agents organize specs |
| G6 | stronger precondition-free version (agent drops a gold precondition the claim does not need) | direction with domain change |

**Bad cases (H₀), certificate = compiled countermodel:**
| Id | Family | Why it matters |
|---|---|---|
| B0 | contradictory premise (`False → G`) and unsatisfiable `A` | must earn no credit (the non-vacuity condition) |
| B1 | weakened to implementation equality (experiment 12) | exists |
| B2 | drop one conjunct (each conjunct in turn) | most common real failure: a missing property |
| B3 | keep only a single conjunct, or only the trivial ones | partial coverage |
| B4 | mutate one comparison or constant (`<` to `≤`, `+1` to `+2`) | near miss |
| B5 | flip one implication or swap an argument | near miss |
| B6 | narrower domain: add a precondition the gold does not have | agent proves less than the gold claims |
| B7 | wrong vocabulary: swap two predicates of the same type (for example `isSorted` for `isReverseSorted`) | semantic near miss |

**Integrity attacks on the pipeline (no model calls), at least 25 files over at least 5 tasks,** each independently compiled, each of which a valid checker must reject: gold-proof reuse, `True`/trivial targets, `False` or unsatisfiable premise, empty bridge, `native_decide`, added axiom, `sorry`, renamed or shadowed gold names, an adapter that assumes the gold statement, proving the converse instead of the forward direction, theorem restatement that weakens the goal, `set_option`/macro/`open ... in` hijack, `unsafe`/`implemented_by`/`extern`, and a copy of the gold inside the agent file. Report the acceptance rate of each pipeline variant: raw saved rule, names-and-axioms gate, repaired fixed-goal checker.

**Provers (budget ladder, one operating point each):**
1. Lean tactics only (`exact id`, `simp_all`, `aesop`, `grind`, `omega`, `decide`, union), no model, free.
2. Pi 1.4.0 + a pinned GPT-6 model, reasoning high, one attempt (no Lean feedback).
3. Same with up to four Lean-feedback rounds (the exp 12 repair budget).
Models (fixed before the run): `gpt-6-astra` for the strongest rung and `gpt-6-luna` as a strength comparator, so the ladder also varies prover strength. Each prover sees only the immutable goal and definitions, never the certificate, never the gold proofs.

**Sample size (design).** At least 100 certified H₁ and 100 certified H₀ cases over at least 6 families each, after ineligibles. Rationale: 0 false alarms in 72 gives an upper bound of 0.05 (two-sided, exact); 100 positives give a half-width near 0.06 at `P_D = 0.9`. If fewer eligible cases exist, report the achieved bound, not the target.

**Metrics.** `P̂_D`, `P̂_F` with Wilson intervals over cases and **cluster-bootstrap intervals over tasks** (10,000 resamples, seed fixed); per family; the (P_F, P_D) point for each budget rung; the Rogan-Gladen corrected coverage for the experiment 145 counted rate (with the transfer caveat); failures listed by reason (no proof, did not compile, forbidden axiom, mapping).

**Pre-registered reading (edit before running; keep the edit in the report).** Call the harsh prover a **supported headline detector** only if all hold: (a) pipeline attack acceptance 0 of at least 25; (b) `P_F` exact upper bound at most 0.05 over at least 72 certified negatives, near-miss families included, with no family above 0.10; (c) `P_D` at the strongest rung at least 0.80 with a cluster interval half-width at most 0.10, and every family reported. Otherwise the headline wording is "verified directional coverage under a fixed budget, lower bound" and the failing criterion is named. A bad case credited by the prover (any false alarm) is a bug report first: inspect it, then decide whether it is a pipeline defect or a prover defect.

## 5. Budget, funding and safety (protocol)
- **Named-key authorization.** Brando, 11-04-2026: "I plan to use the harsh prover (eg [Pi] + anthropic vals api key + high) to do these experiments." After that Vals Anthropic key proved invalid (Status, 15:20), Brando wrote: "koyejo lab keys are fine." Free key checks (`GET /v1/models`, no billing, 11-04-2026): the Vals Anthropic key and both Koyejo-lab Anthropic key files return HTTP 401; the Koyejo-lab OpenAI key (`openai_bm_key_koyejolab.txt`) returns HTTP 200 and lists `gpt-6-astra`, `gpt-6-sol`, `gpt-6-luna`. **Route:** Pi 1.4.0, provider `koyejolab-openai-bm` (the Koyejo-lab OpenAI key; the payer is the Koyejo lab, not Vals), tools disabled, reasoning effort high. This replaces the Anthropic model Brando first named, because no working Anthropic key exists; a working Anthropic key would restore it. No personal key (`personal-openai-brando`), no Vals key, no Valkyrie bypass, no other experiment.
- **Justification (Rule 72 first step).** *Question:* P_D and P_F of the harsh prover. *Decision:* headline wording in the TMLR paper and CLAUDE.md. *Why not existing data:* section 3. *Smallest design:* section 4, with the free rungs (attacks, tactics) run first.
- **Staged and capped.** Preflight = one minimal call plus a positive and a negative control through the exact transport. Pilot = at most 12 cases, hard cap **$30**, then project the measured cost per case before any further batch (batches of at most 25 cases). Total hard cap **$400**, below the $1,000 explicit-go threshold; never estimate from another model or effort (10-21 cascade overspend lesson).
- **Serial calls, one experiment at a time.** No other paid Vals experiment is started by this one; the 10-15 Valkyrie pause is not touched (this route is not Valkyrie, and that is disclosed).
- **Isolation.** The key is read inside the host transport only, never printed, logged, put in a prompt or a file. The Lean child process has network syscalls blocked (experiment 12 `lean_runner.py`). The prover sees no certificate and no gold proof. Gold never edited.
- **Stop rules.** Cap reached, a transport or schema failure (HTTP 4xx other than a counted refusal, key rejected), a checker failure, a false alarm (pause and inspect), or completion. Missing and failed cells stay in the denominator.

## 6. Natural population (the human ratings)
The control suite estimates P_D and P_F on constructed cases. The missing human ratings on real agent outputs supply ground truth for the natural population: run the same prover on those items and compute P_D and P_F against the human label, then test whether the control estimates transfer (Rogan-Gladen needs it). This is the follow-up the controls cannot replace.

## 7. Status
(see the Status section appended by each step; nothing below is a result until it says Lean-checked)
- 11-04-2026: plan written, evidence inventory done (zero model calls).
- 11-04-2026 (clock `date`): Brando chose "prover is headline" and the entailment sections of CLAUDE.md and AGENTS.md record it with required caveats (commit `016487d036`). Two build workers started (certified good/bad case suite; integrity-attack suite), no model calls. Prover route pinned: Pi 1.4.0, provider `vals-anthropic-bm` (the Vals route; the `koyejolab-anthropic-bm` provider that Pi also lists is NOT used), tools disabled, thinking high, models `claude-opus-5-5` (primary) and `claude-sonnet-5-5` (strength comparator), the experiment's own Lean-feedback loop (same prompt and four repair rounds as experiment 12). Pi shell tools are disabled on purpose: an agentic Pi on the host could read oracle certificates or key files. First paid action: one minimal preflight call (below).
- 11-04-2026 15:20 PST: **paid arm blocked at preflight.** One minimal Pi call on the pinned route returned `401 invalid x-api-key` (zero tokens, $0 billed; receipt shape: Pi JSON `stopReason: error`, request id kept off Git). A free `GET /v1/models` check of the same key file (`anthropic_vals_ai_key.txt`, same SHA-256 prefix on the Mac and skampere2) returned HTTP 401 twice, so the key itself is rejected by Anthropic, not Pi, the model id or the host. Per the funding rule no new calls are made and no other key is substituted (not the Koyejo-lab provider Pi also lists, not any personal key). Unblock options for Brando: (1) a working Vals-provided Anthropic key in `~/keys/anthropic_vals_ai_key.txt` (Mac and SNAP); (2) a Valkyrie route, which needs his approval under the 10-15 spend gate; (3) accept the free rungs plus a local open-weight prover on SNAP as the harsh prover for this experiment. The case-construction and attack workers keep running (no model calls).
- 11-04-2026 15:57 PST: **route changed, preflight passed.** After "koyejo lab keys are fine", free key checks showed the Koyejo-lab Anthropic keys are also dead (HTTP 401) and the Koyejo-lab OpenAI key is live (HTTP 200). One Pi call (tools disabled) on provider `koyejolab-openai-bm`, model `gpt-6-astra`, reasoning high, returned the requested text with stop reason `stop`, 470 input and 5 output tokens, **$0.00495** (observed price about $10 per million input and $50 per million output tokens). Prover runner written (`scripts/prover_pi_runner.py`), not yet run on any case. Total spend so far: $0.00495. An adversarial design review (five lenses, each finding checked by a skeptic) is running before any pilot; its amendments are applied here before the first case.
- 11-04-2026 16:20 PST: **integrity-attack suite done** (zero model calls, Lean-checked; details `attacks/README.md`, `attacks/attacks.csv`, `attacks/summary.json`). 232 invalid submissions over 11 tasks (212 bridge-file attacks in 20 classes plus 20 fixed-goal probes) and 35 valid controls; gold sha256 unchanged. Accepted invalid submissions (a false alarm; Wilson 95%): (a) raw saved terminal rule 179/212 (0.844 [0.789, 0.887]); (b) names and axioms gate 155/212 (0.731 [0.668, 0.786]); (c) the experiment 12 repaired fixed-goal checker, unchanged, 8/72 (0.111 [0.057, 0.204]) on the 4 tasks where a fixed goal was prepared; (c') (c) plus a nonce-bound axiom audit 0/72 (0.000 [0, 0.051], this patch is tested only on these 100 submissions). Valid controls accepted: (a) 7/7, (b) 7/7, (c) and (c') 28/28. **Defect found in (c):** its axiom audit parses printed Lean output, and a line `'X' does not depend on any axioms` printed by the submission itself (for example `by trace "..."; exact sorryAx _ false`) overrides the real audit, so a `sorry` proof is accepted; all 8 acceptances are this one mechanism. I reproduced the parsing defect independently in pure Python: the experiment 12 `audit()` returns `[]` axioms for a log holding both the forged line and the real `depends on axioms: [sorryAx]` line, in either order. The same weakness exists in any pipeline that parses printed audit lines, including experiment 145's; exposure check (script over text): none of the 1,023 experiment 142 bridge files contains an audit-line string or an output-printing command (`trace`, `logInfo`, `run_cmd`, `#eval`, `IO.println`, `dbg_trace`); the solver agents' own files are not in the repository and were not scanned (not checked). Classes expressible against an immutable goal are the only ones (c) can see; the statement-level attacks (shadowed names, assumed gold, converse, tautology) are reported for (a) and (b) only. Pre-registered criterion (a) ("pipeline attack acceptance 0 of at least 25") **fails for the unmodified checker** and is met only by the patched checker, which counts as a separate condition.

**TLDR-end:** [veribench: harsh prover P_D/P_F] Verdict: the existing 24/24 and 0/19 controls are not enough for a paper; the plan adds certified good/bad families, a wider attack suite, and the intended Pi + Anthropic prover under a $400 capped, staged protocol.
