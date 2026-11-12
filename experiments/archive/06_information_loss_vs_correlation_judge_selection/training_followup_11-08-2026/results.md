<!-- TLDR: Weighted training and stable Pearson fitting are complete and verified; observed weighted-loss improvement is statistically unresolved. -->
# Live results — weighted training

**Status: COMPLETE, verified 11-08-2026.** Source frozen at `6e8f609`; run finished in 56.288 seconds. All 50 primary mixture fits passed certificates and all 900 softmax fits converged. Independent reconstruction passed for all 175 final models and 2,625 forecast rows.

Weighted mixture test loss: **0.191659**, versus **0.202068** for the matched Pearson mixture. Paired difference: **−0.010409 [−0.061911, +0.005933]**, 95% task-family bootstrap with mixture refitting; 998/1,000 valid draws, two certificate failures retained; p-val=n/a. This does not resolve an advantage.

See [full results](RESULTS_training.md), [protocol](PROTOCOL.md), [aggregate evidence](results/results.json), [verification](results/verification.json) and [resample verification](results/verification_refit_samples.json). Zero new inference calls; $0 provider inference charges. Historical sample, not fresh judge validation.
