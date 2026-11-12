# Offline preparation and evaluation for six-probability judges

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/native_probability/README.md>

**TLDR:** This executable scaffold hashes supplied artifacts, strictly parses six-category probability forecasts, and scores individual ratings with the same evaluation for method 2 and method 4. It implements no model transport, training, selection, collection, or validated judge; its tests use synthetic temporary files only.

## Scope and boundaries

The [parent design](../README.md) remains prospective. Normalized ranked probability score (RPS) remains its primary endpoint. Method 2 means correlation training; method 4 means proper-loss training. Both can supply forecasts to this identical evaluator, but method metadata is only a declaration, not proof that training occurred. `fixed_baseline` is also accepted. Existing model choices, inference budgets, collection assignments, and sealed-data rules are unchanged.

Cross-entropy (CE) and total variation distance (TVD) are secondary evaluation metrics in the common panel. RPS remains the common validation criterion; this module does not perform that selection. Reports mark this panel with `metrics_version: native_probability_metrics_v2`. The input-manifest format remains `native_probability_offline_v1`; completed experiment protocols and results retain their original definitions.

One manifest represents one judge configuration, one split, and one forecast per artifact. Repetitions or different configurations require separate manifests; this module does not aggregate repeated model calls or select a winner. The artifact identity includes task-family and agent identifiers, but this module does not create or certify disjoint splits. Rater identifiers are opaque observation keys, not evidence of qualification or consent.

The supported visibility is the parent's current `complete_candidate_and_reference_artifacts_including_proof_bodies`. Exact supplied files are hashed without extracting, editing, or interpreting Lean. Their hashes do not establish semantic correctness. The caller supplies the declared prompt digest; only future transport can bind an actual model request to the rendered prompt and these inputs.

Real inputs, responses, individual ratings, and receipts belong in an authorized private store. They are not publication artifacts. This folder contains no real ratings or inference outputs. Evaluating an explicitly supplied file does not grant permission to open a sealed test or turn an inherited evaluation-only round into training data.

## Minimal schema

`scaffold.py freeze` reads a specification of this form. All shown values are synthetic placeholders:

```json
{
  "condition_id": "synthetic_control",
  "split": "train",
  "proof_visibility": "complete_candidate_and_reference_artifacts_including_proof_bodies",
  "judge_configuration": {
    "judge_id": "synthetic_judge",
    "model_id": "none_synthetic",
    "harness": "offline_control",
    "effort": "not_applicable",
    "training_method": "fixed_baseline",
    "prompt_sha256": "0000000000000000000000000000000000000000000000000000000000000000"
  },
  "artifacts": [{
    "artifact_id": "a0",
    "task_family_id": "f0",
    "agent_id": "synthetic_agent",
    "files": {
      "python_source": "source.py",
      "candidate_lean": "candidate.lean",
      "gold_reference_lean": "reference.lean",
      "rubric": "rubric.md"
    }
  }]
}
```

Replace the placeholder digest with the actual prompt digest for a real condition. Allowed splits are `train`, `validation`, and `test`. Allowed training-method labels are `method_2_correlation`, `method_4_proper_loss`, and `fixed_baseline`. Paths must resolve inside `--input-root`, including through symlinks. The frozen manifest records each file's byte count and SHA-256, each artifact's input digest, and a digest of the complete manifest. These are integrity checks, not digital signatures or proof of model execution.

Responses are a JSON array. Each envelope contains exactly `artifact_id`, `input_sha256`, `manifest_sha256`, and either `response` or `error`. The hash fields must match the frozen manifest. `response` is the raw model-response string; `error` is a nonempty failure-category string, such as `transport_timeout`. Example raw response:

```json
{"probabilities": [0.1, 0.2, 0.3, 0.1, 0.2, 0.1], "rationale": "Synthetic parser example."}
```

The parser accepts exactly those two keys and six finite numeric entries in [0,1]. **Their decimal JSON values must sum exactly to one.** There is no normalization, clipping, probability floor, prose extraction, or repair. Rounded vectors totaling 0.999999 are invalid. Duplicate keys, booleans as probabilities, nonfinite constants, extra keys, and underflow to floating-point zero are rejected. A blank or malformed response is an `invalid` scheduled forecast, not a reason to remove the artifact.

Ratings are a separate JSON array with exactly `artifact_id`, `input_sha256`, `rater_id`, and `rating` per observation. `rating` must be an integer 0–5. Its input digest binds the observation to the same artifact packet independently of the judge configuration. Repeated artifact/rater pairs, unknown IDs, and mismatched hashes are structural input errors and stop evaluation; they are not silently ignored or treated as extra independent observations. Distinct rating occasions would need a separately specified observation schema.

## Commands and bounded operation

Run the synthetic controls from the repository root:

```sh
python3 -B -m unittest discover -s experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/native_probability -p 'test_*.py' -v
```

The offline interface, for already authorized local files, is:

```sh
python3 -B experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/native_probability/scaffold.py freeze \
  --spec /absolute/research_artifacts/spec.json --input-root /absolute/research_artifacts/inputs \
  --out /absolute/research_artifacts/manifest.json
python3 -B experiments/02_design_a_judge_that_predicts_human_ratings_0_to_5_start_06Nov2026/native_probability/scaffold.py evaluate \
  --manifest /absolute/research_artifacts/manifest.json --input-root /absolute/research_artifacts/inputs \
  --responses /absolute/research_artifacts/responses.json --ratings /absolute/research_artifacts/ratings.json \
  --out /absolute/research_artifacts/evaluation.json
```

These example paths are placeholders, not files delivered with this scaffold. Output files are created exclusively and never overwritten. Limits are 10,000 scheduled artifacts, 100,000 individual ratings, 16 MiB per input file, 32 MiB per JSON input, and 64 KiB per raw forecast. These are software limits, not experimental sample sizes or spending authorizations. There is no networking, provider key loading, retry, model inference, or fitting code.

The standard library implements preparation, parsing, losses, and Pearson correlation. SciPy supplies Spearman correlation with average ranks for ties and Kendall tau-b. Its runtime version is recorded when those diagnostics run. If SciPy is absent or cannot load, those two results are explicitly unavailable; the report does not claim a complete correlation panel. Constant scores or fewer than two scored artifacts make all correlations undefined (`null`).

## Metrics and the experiment 07 crosswalk

For artifact i, the forecast is q over ratings 0–5, and p is the empirical histogram of its individual human ratings. Let Q and P be their cumulative sums through categories 0–4. Each proper loss is computed against **each individual rating**, averaged within artifact, and then averaged equally across artifacts. Raters' ordinal values are not averaged before calculating a proper score.

| Report field | Definition | Range / interpretation |
|---|---|---|
| `rps` | Mean over ratings of `(1/5) sum_c (Q_c - 1{rating <= c})²` | [0,1]; primary proper score, includes human disagreement |
| `ce` | Mean over ratings of `-ln(q_rating)` | [0,+infinity]; natural-log cross-entropy, no probability floor |
| `tvd` | `(1/2) sum_r abs(q_r-p_r)` per artifact, then equal artifact mean | [0,1]; secondary distance to the empirical human rating distribution, lower is better |
| `brier` | Mean over ratings of `sum_r (q_r - 1{rating=r})²` | [0,2]; six-category convention, not binary Brier |
| `empirical_cdf_squared_distance` | `(1/5) sum_c (Q_c-P_c)²` | [0,1]; distance to a noisy empirical rating histogram |
| `empirical_disagreement` | `(1/5) sum_c P_c(1-P_c)` | Artifact's empirical disagreement contribution |
| `root_mean_cdf_distance` | Square root of the artifact mean of `empirical_cdf_squared_distance` | Corresponds to experiment 07's `sqrtRPS` distance convention, **not** square root of raw proper RPS |
| `kl_human_to_judge` | `ce - human_entropy`, with entropy `-sum_r p_r ln(p_r)` | Forward Kullback–Leibler divergence to the empirical histogram |
| `nrmse` | Square root of artifact mean squared error between expected judge rating/5 and human mean rating/5 | [0,1]; normalized root mean squared error |
| `mae`, `bias` | Absolute error and signed judge-minus-human error between those normalized means | Bias is positive for higher judge ratings; both means are reported |
| `pearson`, `spearman`, `kendall_tau_b` | Correlations of those paired artifact means | Diagnostics of scalar agreement, not identification of the full distribution |

The checked identity is `rps = empirical_cdf_squared_distance + empirical_disagreement`. Therefore raw RPS and empirical cumulative-distribution distance give identical ordering on the **same artifacts and individual ratings**, but their values differ. Rooting the latter after averaging also preserves that ordering. This statement does not apply to unmatched scored subsets or different weighting. See [experiment 07](../../archive/07_compare_5_judges_on_75_outputs_and_estimate_rating_needs/results.md) for its historical notation; this scaffold does not rename that frozen result.

TVD uses the empirical distribution within each artifact, not a pooled distribution across artifacts or an average of distances to individual point-mass ratings. Sparse empirical human distributions are noisy. TVD is a secondary distribution diagnostic, does not use rating order, and is distinct from total variation distance mutual information (TVD-MI), which measures dependence. It does not replace the primary proper RPS.

Assigning zero probability to any observed category yields infinite artifact CE and forward divergence. Standard JSON cannot encode infinity as a numeric token, so reports use the explicit string `"Infinity"`; they never substitute a finite cap or `null`. Unsupported observations are counted. Small positive probabilities remain positive unless they cannot be represented by the scoring floating-point type, in which case parsing fails explicitly.

## Failure accounting and interpretation

The frozen manifest supplies the full scheduled denominator. Each scheduled artifact receives `ok`, `invalid`, `error`, or `missing` response status. An artifact without human ratings also remains scheduled and unscored. One unknown or duplicate response ID stops evaluation as a manifest error rather than allowing ambiguous matching.

`scored_artifacts_only` contains diagnostic means over artifacts with both a valid forecast and at least one rating. `point_estimates_cover_full_manifest` is true only when every scheduled artifact is scored. The report also provides full-denominator lower/upper bounds using ranges [0,1] for RPS, TVD and squared errors, [0,2] for multiclass Brier, and [0,+infinity] for CE. These bounds retain failures without inventing replacement probabilities or a final missingness policy. They are **not confidence intervals**. No statistical acceptance threshold, uncertainty estimate, or winner is implemented.

Every report binds the manifest, raw response bundle, rating bundle, and forecast receipt by SHA-256. It rechecks current input-file bytes before scoring. The caller retains the original input bundles privately so those hashes can be independently reconstructed. No per-rater values are echoed into the report, but probability vectors and derived information can still be sensitive; the report is private by default.

File hashes cover exact file bytes, and each raw response hash covers its exact UTF-8 text. Structured manifest/bundle/receipt digests use `encoded()`'s canonical JSON: sorted object keys, compact separators, UTF-8, and no nonfinite numeric tokens. They therefore do not hash incidental whitespace in an enclosing JSON file.

## Predicted synthetic controls

These expectations are written in `test_scaffold.py`; they concern parser and arithmetic correctness, not semantic judge performance.

| Control | Expected result |
|---|---|
| Point mass on observed rating | RPS, CE, TVD, Brier, empirical distance, and normalized mean error all zero |
| Point mass at 0, observation 5 | RPS 1; TVD 1; Brier 2; CE infinite; normalized squared mean error 1 |
| Half mass at 0/5, human observations 0 and 5 | RPS 0.25; TVD 0; empirical distance 0; CE ln(2); forward divergence 0; Brier 0.5 |
| Half mass at 0/5, human observations 0, 0, 0 and 5 | TVD 0.25, not the 0.5 average distance to individual point masses |
| Half mass at 1/4, human observations 0 and 5 | TVD 1 because the distributions have disjoint support |
| One zero-loss artifact with one rater, one worst-RPS artifact with three raters | Mean RPS and TVD 0.5, not rating-weighted 0.75 |
| One zero-loss forecast plus invalid/error/missing forecasts, four scheduled artifacts | One scored artifact; RPS and TVD full-denominator bounds [0,0.75] |
| No artifact has ratings | No scored point estimates; TVD full-denominator bounds [0,1] |
| Paired normalized means (0,0,1) and (0,1,1) | Pearson, Spearman, and Kendall tau-b each 0.5 when SciPy is available |
| Changed source bytes, wrong input/condition hash, duplicate observation | Explicit integrity failure |

Transport preflight, actual model identities and costs, prompt fitting, probability mappings, matched method-2/method-4 training, validation selection, new human data, repeatability, confidence intervals, and deployment evidence remain separate work.
