#!/usr/bin/env python3
"""TLDR: Render the public aggregate report directly from the reproducible retrospective result JSON."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NAMES = {'astra': 'GPT-6 Astra / Terminus 2', 'claude_code': 'Opus 5 / Claude Code',
         'codex': 'GPT-5.6 Sol / Codex CLI', 'fable51': 'Fable 5.1 / Terminus 2'}


def display(stat):
    if stat['value'] is None:
        return 'unavailable (constant vector)'
    ci = stat['ci95']
    return f"{stat['value']:.3f} [{ci[0]:.3f}, {ci[1]:.3f}]"


def main():
    data = json.loads((ROOT/'results/retrospective.json').read_text())
    c = data['conditions']['all_agents']
    delta = c['test']['paired_brier_difference']
    text = [
        '<!-- TLDR: A probability map of historical judge-produced scalar formal specification coverage (FSC) ratings predicts historical prover acceptance better than a prevalence constant; this is retrospective operational forecasting only. -->',
        '# Experiment 03: retrospective prover-target results', '',
        f"On 512 historical test artifacts from 128 tasks, a fitted probability map lowers Brier loss by {-delta['value']:.3f} relative to the training-prevalence baseline (difference {display(delta)}, mapped minus constant; p-val=n/a).",
        '',
        'This is a zero-call reanalysis of the archived Tiny256 condition, not a new VeriBench release evaluation, a fresh judge test, or semantic entailment validation. No new language-model forecast was evaluated. The target is experiment 145’s saved five-condition acceptance flag. Existing outcomes had prior exposure, related task families cross splits, and bridge faithfulness remains unverified. An artifact is one solver run on one task.',
        '', '## Scope and selection', '',
        f"Source join: {data['rows']} artifacts, {data['tasks']} task identities, four historical solver configurations, {data['missing_join_rows']} missing joins. Hash split: 64 train, 64 validation, 128 test tasks. The pooled fit has {c['train_artifacts']} training and {c['validation_artifacts']} validation artifacts. Ridge selected by validation Brier loss: {c['selected_ridge']}. Training-prevalence forecast: {c['training_prevalence']:.6f}. The test has {c['test']['positives']} observed successes.",
        '',
        'The map fits logistic log loss on training outcomes, with its ridge strength selected by validation Brier loss. Ridge zero wins all five comparisons; the other tested penalties shrink the slope substantially. This coarse grid does not establish effective regularization selection, and it is retained unchanged. No test refit or threshold search is performed. Historical judge-produced scalar formal specification coverage (FSC) ratings are input features; they were not elicited as prover-success probabilities. The raw scalar row is a diagnostic numerical comparison. Mean absolute error is descriptive only: it is not a proper probability score and is not used for selection.',
        '', '## Pooled retrospective test', '',
        '| Forecast | Brier loss ↓ | Mean absolute error (descriptive) | Bias (forecast − outcome) | Forecast mean | Outcome mean |',
        '|---|---:|---:|---:|---:|---:|',
    ]
    for name, m in c['test']['metrics'].items():
        text.append('| '+name+' | '+' | '.join(display(m[k]) for k in ('brier','mae','bias','mean_forecast','mean_outcome'))+' |')
    text += ['', '| Forecast | Pearson | Spearman | Kendall | Area under receiver operating characteristic curve |', '|---|---:|---:|---:|---:|']
    for name, m in c['test']['metrics'].items():
        text.append('| '+name+' | '+' | '.join(display(m[k]) for k in ('pearson','spearman','kendall','auroc'))+' |')
    text += ['', '## Leave-one-agent-out fitting procedure', '',
             'Each fit excludes the named solver from both training and validation (192 artifacts per split), then predicts its 128 test artifacts. These are four historical configurations, not random draws of future agents.', '',
             '| Excluded configuration | Ridge | Mapped Brier | Constant Brier | Paired difference |', '|---|---:|---:|---:|---:|']
    for key, condition in data['conditions'].items():
        if key == 'all_agents':
            continue
        t = condition['test']
        text.append(f"| {NAMES[condition['excluded_solver']]} | {condition['selected_ridge']} | {display(t['metrics']['mapped']['brier'])} | {display(t['metrics']['constant']['brier'])} | {display(t['paired_brier_difference'])} |")
    text += ['', '## Historical acceptance counts', '',
             'These counts describe source revisions of the operational acceptance rule. They do not measure a new prover, and the five-condition target is not proof-invariant statement coverage.', '',
             '| Configuration (256 artifacts each) | Raw accepted | Conditions 1–4 | Conditions 1–5 (target) |', '|---|---:|---:|---:|']
    for solver, counts in data['acceptance_counts'].items():
        text.append(f"| {NAMES[solver]} | {counts['raw']} | {counts['four']} | {counts['y']} |")
    diag = data['posthoc_diagnostics']
    text += ['', '## Post hoc diagnostics requested in review', '',
             f"A name-based family heuristic finds {diag['families_spanning_splits']} families crossing splits and {diag['test_tasks_with_fit_sibling']}/128 test tasks with a training or validation sibling. It groups security vulnerability number/stem pairs, heap-sort variants and HumanEval numbered variants; exact code is `posthoc_diagnostics` in `scripts/analyze.py`. This is not a complete semantic family classification. The original split and all fits remain unchanged; family transfer and family-independent uncertainty are not established.", '',
             'Forecast accuracy varies by the original judge-produced scalar FSC rating. The following descriptive bands were added after review, not used for selection; small bands and shared tasks limit inference. The near-zero pooled bias conceals overprediction in the 0.9 band. No new probability mapping was fitted to these diagnostics.', '',
             '| Original score | Artifacts | Task identities | Successes | Mean forecast | Observed rate |', '|---|---:|---:|---:|---:|---:|']
    for band in diag['score_bands']:
        text.append(f"| {band['score_band']} | {band['artifacts']} | {band['tasks']} | {band['successes']} | {band['mean_forecast']:.3f} | {band['observed_rate']:.3f} |")
    text += ['', '## Uncertainty and limits', '',
             '- All intervals use 10,000 paired task-clustered bootstrap resamples, seed 11062026, conditional on the fitted models and fixed solver panel. They omit training/selection uncertainty and the detected task-family dependence. Full statistics for every excluded-agent condition are in `results/retrospective.json`.',
             '- p-val=n/a: descriptive retrospective screening, no confirmatory test. Correlations are undefined for the constant forecast. One saved outcome per artifact means repeat-search variance is unavailable.',
             '- The source checker’s name matching and axiom checks do not establish statement/adapter faithfulness. Its source flags 51/789 accepted natural artifacts with some hypothesis-independent reference proofs (two with all), by a text heuristic. The analogous names-and-axioms gate accepted 155/212 constructed invalid bridges; a forged-audit weakness is explicitly applicable to the source145 pipeline. A scan found no printing/audit-string patterns in 1,023 bridges, but candidate solver files were not scanned. These are integrity limitations, not a measured semantic error rate on the 1,024 artifacts; see SOURCE_AUDIT.md.',
             '- Source outcomes include candidate-proof axiom filters, representation choices and variable historical authoring budgets; the exact deployed prover model/effort was not recorded in the source 142 protocol. The `tc` manifest does not bind an exact judge model per artifact. Source140 already reported feature-versus-precursor-outcome associations, and source142 does not establish whether bridge authors saw `tc`. These limitations preclude an exact modern model comparison.',
             '- No human ratings, candidate code, private task identities or per-artifact outputs are exported. The protected source blobs and exact split manifest remain under `research_artifacts/prover_target/`.',
             '- New measured model calls: 0. Incremental measured-inference cost: $0. Producing the historical judge-rating feature had a prior cost; this analysis does not measure end-to-end cost savings. Funding pause remains in force; exact gate paths/hashes are in `sources/funding_gate.json`, and its scoped exceptions were not expanded.',
             '', '## Decision', '',
             'The retrospective screening criterion is met: the pooled paired interval is below zero. This supports further study of a cheap operational forecasting target. It does not establish that a new language-model probability judge works, that the target equals semantic entailment, or that the human-rating study can be replaced without changing its question.',
             '',
             'Copy-ready collaborator message: “I tested a no-new-call fallback: learn the probability that a fixed prover accepts a specification implication. Historical coverage ratings contain useful predictive signal, but the current outcomes depend on proof and adapter rules, so the next study needs a faithful statement-only protocol and a fresh test.”',
             '',
             '**TLDR-end:** [ttj: prover-target study] A zero-call retrospective probability map improves prediction of saved prover acceptance. The deliverable is an operational forecasting feasibility result, not fresh semantic or human validation.', '']
    (ROOT/'RESULTS.md').write_text('\n'.join(text))
    print(ROOT/'RESULTS.md')


if __name__ == '__main__':
    main()
