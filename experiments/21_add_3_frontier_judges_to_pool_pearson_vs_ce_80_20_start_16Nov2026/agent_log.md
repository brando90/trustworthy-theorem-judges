# Run log, 16 Nov 2026

- Judge calls: 3 judges × 75 artifacts × 3 repeats = 675 calls, all COMPLETE, concurrency 6, each with a per-judge cost cap (Astra \$60, Sol 6.1 \$25, Argon \$40; none reached). Estimated spend from the ledger: Astra \$10.70, Sol 6.1 \$1.86, Argon \$7.49; summed from per-call usage in `results/judge_scores.csv`: \$10.82, \$1.88, \$7.53 = \$20.23.
- Routes: OpenAI Responses API (Koyejo-lab key) and Gemini generateContent API. No Anthropic key worked (every key returned an invalid-key error), so no new Opus judge.
- Pool analysis: `run_exp12.py` on three pools (old 5, new 3, all 8), 1,000 splits, 10,000 bootstrap draws; transcripts in `results/run_transcript_*.txt`.
- Agents: one gpt-6-astra agent per method on the fixed split (seed 1210), each seeing only the 60 train artifacts. ② agent: nonnegative least squares projection, train Pearson 0.8309, cost \$0.12. ④ agent: SLSQP from 50 starts plus a KKT check, train CE 1.5178, cost \$0.16. The ② agent's weights equal the coded optimizer's; the ④ agent put 0.57 on the train marginal, which the coded ④ optimizer's mixture did not.
- A first attempt with the Codex CLI did not run (its sandbox could not start on the host), so the custom tool loop was used.
