<!-- TLDR: This separately frozen historical-data condition compares weighted probability training with a stable Pearson mixture and four matched softmax objectives. -->
# Weighted training follow-up — 11-08-2026

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/training_followup_11-08-2026/README.md>

The user requested weighted probability mass function (PMF) training and a stable correlation baseline on current data. The primary comparison fits the same five-judge mixture under weighted squared PMF loss and Pearson correlation. The secondary comparison fits the same softmax family under weighted loss, cross-entropy, Brier loss and ranked probability score. This trains small numerical mappings of cached judge ratings; it does not train a language model.

Read [PROTOCOL.md](PROTOCOL.md), [protocol.json](protocol.json) and [MATH_baseline.md](MATH_baseline.md) for the design, controls, numerical guarantees and limitations. [results.md](results.md) tracks execution; [CKPT_training_followup.md](CKPT_training_followup.md) preserves continuation state. This condition uses already inspected historical ratings, so a family-held-out result is exploratory and does not provide fresh judge validation.

## Directory structure

- `PROTOCOL.md`, `protocol.json`: frozen procedure, counts, seeds and limits.
- `MATH_baseline.md`: matched mixture derivation and optimality checks.
- `scripts/PROMPT_*.md`: execution and implementation prompts.
- `scripts/mixture_models.py`, `check_mixtures.py`: exact mixture fits and synthetic controls.
- `scripts/weighted_softmax.py`: four softmax losses and gradient controls.
- `scripts/run_training.py`, `supervise.py`: fixed manifest, bounded execution and receipts.
- `scripts/verify_training.py`: independent reconstruction and metric verification.
- `results/`: aggregate preflight, launch, progress, terminal and final evidence.
- `results.md`, `RESULTS_training.md`, `CKPT_training_followup.md`: live state, final report and checkpoint.

Input ratings, per-artifact forecasts, fitted model weights and bootstrap arrays remain in ignored `private/06_information_loss_vs_correlation_judge_selection/training_followup_11-08-2026/` in the canonical repository. Historical input hashes and aggregate evidence are public; private input bytes are not.

## Execution

Run from this phase's parent experiment directory on the recorded remote host. The supervisor takes the private dataset path, private output directory and frozen Git revision:

```sh
python3 training_followup_11-08-2026/scripts/supervise.py DATASET_JSON PRIVATE_OUTPUT FROZEN_REVISION
```

It refuses to replay a recorded launch. The only numerical worker is ordinary Python in a named persistent session, one CPU thread, at most 7,200 seconds and zero provider inference calls. A later rerun requires a separate condition and receipts. Verification does not refit or modify the recorded condition.
