#!/usr/bin/env python3
"""TLDR: Assemble the two-condition outcome without presenting degenerate conditional loss as judge validation."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PRIVATE=ROOT.parents[1]/'private/fresh_prover_target'
def read(p):return json.loads(p.read_text())
def main():
 v1=read(ROOT/'results/analysis.json');v2=read(ROOT/'conditions/nonthinking_v2/results/analysis.json');verification=read(ROOT/'results/verification.json')
 artifacts=read(PRIVATE/'v2/artifacts.json');targets=read(PRIVATE/'v2/targets.json');states=[read(PRIVATE/'run_state.json'),read(PRIVATE/'v2/run_state.json')]
 available={t['artifact'] for t in targets if t['target'] is not None}
 summary={'conditions':[v1['condition'],v2['condition']], 'verdict':'no validated judge; local feasibility failed to provide outcome variation and sufficient valid outputs',
  'attempted_artifacts':8,'unique_statement_hashes':v2['availability']['unique_statement_hashes'],
  'unique_context_source_hashes':v2['availability']['unique_context_hashes'],
  'well_formed_artifacts':len(available),'unique_well_formed_statements':len({a['statement_sha256'] for a in artifacts if a['id'] in available}),
  'source_task_families':4,'families_with_available_targets':len({a['task_id'] for a in artifacts if a['id'] in available}),
  'successful_targets':v2['availability']['target_successes'],'invalid_candidates':8-len(available),
  'primary_forecasts_planned':16,'primary_forecasts_available':sum(r['J0'] is not None for r in v2['artifacts'])+sum(r['J1'] is not None for r in v2['artifacts']),
  'shared_calls':verification['shared_calls'],'shared_requested_output_tokens':verification['shared_requested_tokens'],
  'shared_observed_output_tokens':sum(a['cost']['observed_output_tokens_terminal_records'] for a in [v1,v2]),
  'shared_wall_seconds':verification['shared_elapsed_seconds'],'provider_cost_usd':0,
  'thinking_characters_v1':v1['cost']['thinking_characters_terminal_records'],'thinking_characters_v2':v2['cost']['thinking_characters_terminal_records'],
  'reporting_qualification':'post-outcome support-count clarification; frozen analysis code and losses unchanged','judge_support':{},'roles':{},'model':'qwen3.5:9b-q4_K_M','model_digest':read(ROOT/'config.json')['model_digest']}
 calls=[r for s in states for r in s['calls'].values()]
 for role in ['preflight','generation','forecast','proof_search']:
  rs=[r for r in calls if r['role']==role];summary['roles'][role]={'calls':len(rs),'completed':sum(r['status']=='completed' for r in rs),'requested_output_tokens':sum(r['num_predict'] for r in rs),'observed_output_tokens':sum(r.get('eval_count') or 0 for r in rs)}
 for j,stat in v2['judges'].items():
  available_rows=[r for r in v2['artifacts'] if r[j] is not None and r['target'] is not None]
  summary['judge_support'][j]={'paired_artifacts':len(available_rows),'observed_families':len({r['task'] for r in available_rows}),'valid_bootstrap_draws':stat['brier_bootstrap']['valid_resamples'],'dropped_empty_draws':10000-stat['brier_bootstrap']['valid_resamples'],'inferential_interval':None,'reason':'insufficient family support and constant outcomes/forecasts'}
 diagnostics=ROOT/'results/diagnostics.json'
 if diagnostics.exists():summary['independent_counterexamples']=read(diagnostics)
 (ROOT/'results/summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 rows=['<!-- TLDR: The completed local pilot did not validate a judge: malformed statements and a single observed outcome class prevent a nontrivial comparison. -->',
 '# Fresh local prover-target judge results','',
 '**Status, 11-06-2026: completed local feasibility test; no validated judge or winner.** The original thinking-enabled condition failed preflight. Its separately frozen non-thinking recovery finished all declared cells, but five statements were malformed and all three available bounded-prover outcomes were 0. Every parsed judge probability was also 0. The prespecified constant-zero baseline matches both judges.','',
 '## Complete artifact ledger','',
 'There were eight generation attempts on four purposively selected, previously exposed task families, with seven unique statement/context-source hashes. Only three artifacts were well formed: two duplicate statements from one task plus one statement from another. Thus there are two unique well-formed statements on two families, not eight independent test items.','',
 '| Artifact | Statement/context | Prover outcome | J0 direct | J1 checklist |', '|---|---|---:|---:|---:|']
 for r in v2['artifacts']:
  status='well formed' if r['target'] is not None else 'invalid syntax/type'
  if r['artifact']=='T01_G1':status+='; duplicate of T01_G0'
  rows.append(f"| {r['artifact']} | {status} | {r['target'] if r['target'] is not None else 'missing'} | {r['J0'] if r['J0'] is not None else 'missing (token cap)'} | {r['J1'] if r['J1'] is not None else 'missing'} |")
 rows+=['','J0 and J1 are direct/checklist prompt configurations of the same Qwen3.5 9B Q4_K_M backbone, both with thinking disabled, capped at 256/1,024 output tokens. Generator prompts also share that backbone. Fourteen of sixteen forecasts parsed; the two missing J0 forecasts exhausted their frozen token limits and were not retried. Prefix-name syntax and extra nested lambdas account for the invalid contexts. They are not encoded as failed semantic implications.','',
 '## Proper loss and missingness','',
 '| Forecast | Available probability/outcome pairs | Conditional Brier | Full eight-artifact Brier bounds |','|---|---:|---:|---|']
 for j,s in v2['judges'].items():rows.append(f"| {j} | {s['observed_pairs']}/8 | {s['brier']:.4f} | {[round(v,5) for v in s['full_denominator_brier_bounds']]} |")
 for b,s in v2['baselines'].items():rows.append(f"| Fixed {b} | {s['observed_pairs']}/8 | {s['brier']:.4f} | {[round(v,5) for v in s['full_denominator_brier_bounds']]} |")
 rows+=['','Conditional mean probability, mean target, signed bias and descriptive mean absolute error are all 0 for each judge, on only 1 paired artifact for J0 and 3 for J1. J0 versus J1 has only one shared available artifact. These zeros provide no evidence of useful discrimination: the outcome and forecast classes are constant, so Pearson, Spearman, Kendall and area under the receiver operating characteristic curve are unavailable. No repeated-forecast variability was measured in the recovery.','',
 'Inferential intervals are unavailable. J0 has one observed family and J1 has two. Of 10,000 bootstrap draws, J0 retains 6,843 and drops 3,157 empty draws; J1 retains 9,375 and drops 625. The frozen four-family bootstrap mechanically returns [0,0] for observed judge losses; this is a degenerate resampling result, **not a precision or population-accuracy claim**. Empty resamples and their counts are explicit in [the detailed analysis](conditions/nonthinking_v2/results/analysis.json), p-val=n/a. The displayed bounds are hypothetical completed-loss bounds: if every missing cell had a defined binary target and forecast, its loss could lie anywhere in [0,1]. These are not confidence intervals, and malformed artifacts do not acquire a defined semantic score through this calculation. Missing outcomes or forecasts are never assigned zero. This support-count qualification was added after execution; the frozen analysis script and computed losses are unchanged. Brier is primary; absolute error is descriptive. No human ratings are used or replaced.','',
 '## Target interpretation and controls','',
 'The new local condition requires independently checked proofs of both candidate consistency and implication to every exported reference obligation. Its immutable statements, separate trusted kernel replay, exact goal types and axiom filter passed four source-context replays and fifteen designed controls. All six local-model proof attempts on the three valid artifacts returned parseable proof JSON but their proof terms were rejected; the fixed tactics also failed. Therefore these outcomes are bounded-search failures. A failed search alone says nothing conclusive about semantic entailment.','']
 if diagnostics.exists():
  d=read(diagnostics);rows.append(f"Separate post-outcome diagnostics checked {sum(r['independent_counterexample_checked'] for r in d['rows'])}/{len(d['rows'])} counterexamples for the unique well-formed statements. Each certificate also supplies satisfying candidate functions, so these cases are consistent but do not imply the gold. The duplicate T01_G1 shares the exact T01_G0 statement/context hashes. These diagnostics never entered judge inputs and do not alter any operational target. See [diagnostic hashes](results/diagnostics.json).")
 rows+=['','This is a distinct local prover condition, not VeriBench experiment169’s Pi/Gemini target. Source169 retains all 100 cases: 14 emitted contexts and 86 unresolved. This pilot selected four emitted cases for simple interfaces and makes no natural-population, frontier-model or unseen-task-family claim. The larger family-disjoint evaluation in [experiment04](../04_fresh_prover_target_judge_validation/PLAN.md) remains unfinished.','',
 '## Shared accounting and audit','',
 f"Both conditions together reserved {summary['shared_calls']}/56 calls and {summary['shared_requested_output_tokens']:,}/81,920 requested output tokens, with {summary['shared_observed_output_tokens']:,} observed output tokens in terminal receipts. Provider charges were $0; measured execution elapsed {summary['shared_wall_seconds']:.2f} seconds ({summary['shared_wall_seconds']/60:.2f} minutes), excluding preparation and review. Hardware use is not an end-to-end cost-saving result. No cap was reset and no failed measured cell was retried.",'',
 'The first condition used eight preflight calls, with six completed responses and two output-token failures; it generated no fresh artifact. The recovery used 38 calls: eight preflight, eight generation, sixteen forecast and six proof requests. Its preflight passed all eight checks. Actual model/server identities, combined token counts and thinking-character counts are retained; the server did not expose separate thinking-token counts.','',
 '- [Shared summary](results/summary.json) and [receipt verification](results/verification.json).',
 '- [Original failed condition](results/v1_results.md) and its unchanged [freeze](sources/freeze.json).',
 '- [Recovery protocol](conditions/nonthinking_v2/PROTOCOL.md), [freeze](conditions/nonthinking_v2/sources/freeze.json) and [detailed report](conditions/nonthinking_v2/results.md).',
 '- [Reproduction runbook](RUNBOOK.md). Raw inputs, statements, proof attempts, model streams and certificates remain private.','',
 '**TLDR-end:** [ttj: fresh local prover-target judges] The fresh local experiment is complete, with immutable target checks and full failure accounting. It did not identify a validated AI judge; a larger, distinct-outcome evaluation remains necessary.']
 (ROOT/'results.md').write_text('\n'.join(rows)+'\n')
 print(json.dumps({k:v for k,v in summary.items() if k not in {'roles','independent_counterexamples'}}))
if __name__=='__main__':main()
