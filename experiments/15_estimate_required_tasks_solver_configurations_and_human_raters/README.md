# Estimate required tasks, solver configurations and human raters

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/15_estimate_required_tasks_solver_configurations_and_human_raters/README.md>

**TLDR:** Finish the current 108-rating evaluation packet; do not adopt a larger total yet. How many held-out task families a later study needs depends on one unmeasured quantity, and existing evidence puts it anywhere from 3 to 155 families for a ±0.01 comparison, with 37 as the middle case. None of the recovered Claude, Gemini or ChatGPT totals establishes statistical sufficiency.

**Status, 11-11-2026:** source recovery and a costed allocation from existing evidence are complete; the final study size is an open decision for Brando (three choices below). No new ratings, judge training, model inference or fitted scaling law are reported here. Experiment 02 (`02_design_a_judge_that_predicts_human_ratings_0_to_5`) owns the judge methodology; experiment 09 (`09_prepare_packets_and_collect_human_ratings`) owns the current packet and collection.

T counts tasks, A fixed solver configurations, H distinct human raters and m ratings per returned file. Count T in independent task families. Ratings collected are files × m, not T × A × H.

## Decision at a glance

Every number below is planning arithmetic from saved results, reproduced by [`scripts/costed_allocation.py`](scripts/costed_allocation.py) into [`results/costed_allocation.json`](results/costed_allocation.json). The [methods note](METHODS_AND_ALLOCATION.md#costed-allocation-from-existing-evidence--11-11-2026) gives inputs, formulas and limits. RPS is the normalized ranked probability score, range 0–1, lower is better.

| Question | What existing evidence supports |
| --- | --- |
| What do we collect now? | Experiment 09's current packet: **25 tasks, three represented solver configurations, 54 returned files, m = 2, 108 independent ratings**; Brando's up-to-54 author ratings are additional. No change proposed. |
| What can those 25 tasks resolve? | A paired RPS difference between two judges to about **±0.012** (95% half-width) in the middle case, ±0.003 to ±0.025 across the three variability cases. One judge's RPS level to about ±0.026. |
| Is that enough to compare training with Pearson correlation (method 2) against training with a proper loss (method 4)? | Only for a large gap. In the archived cached-judge study the gap was 0.024 with 4 training tasks and 0.006 with 20. Middle case, 80% power: 13 task families detect 0.024, 49 detect 0.012 and 234 detect 0.006. |
| How many held-out task families for a chosen precision? | ±0.02: **10** (range 1–39). ±0.01: **37** (range 3–155). ±0.005: **145** (range 11–620). |
| How many training tasks? | The cached five-judge mixture was 0.0021 RPS above its 20-task value at 12 training tasks and 0.0006 above at 16. Nothing is measured beyond 20 tasks or for a larger judge family. |
| How many ratings per file? | Keep m = 2. Training on one rating per file instead of the available 2–3 cost 0.0020 RPS; two instead of 2–3 cost 0.0004. Extra tasks buy more than extra ratings per file. |
| How many solver configurations? | Treat A as named fixed conditions and report per configuration. Three or four configurations cannot support an interval over unseen solvers. |
| How many people? | H follows from workload. 108 ratings are 27, 14 or 9 each for 4, 8 or 12 people. |
| How long does one rating take? | **Unmeasured for the main task.** The only entered times are one rater's six warm-up files: median 4 minutes, range 2–5. Main-task candidate files are 7.7 times longer by median line count (448 versus 58 lines). |

### Costed scenarios

Hours use two bracketing cases: 4 minutes per rating (the measured warm-up median) and 31 minutes (an assumption that time scales with file length). Neither measures the main task. New tasks are costed at the packet's measured 2.16 returned files per task.

| Scenario | Held-out tasks | Independent ratings | Hours, 4 to 31 minutes each | Ratings each, 4 / 8 / 12 people |
| --- | ---: | ---: | --- | --- |
| Finish the current packet | 25 | **108** | 7 to 56 | 27 / 14 / 9 |
| Add a 24-task development pool (16 training, 8 validation) | 25 | 212 | 14 to 109 | 53 / 27 / 18 |
| Development pool, plus held-out tasks for ±0.01 | 37 | 264 | 18 to 136 | 66 / 33 / 22 |
| Development pool, plus held-out tasks for ±0.005 | 145 | 732 | 49 to 377 | 183 / 92 / 61 |

The 24-task development pool is an agent-suggested starting block, not a derived requirement. The held-out counts use the middle variability case; the low and high cases change them by a factor of about 13 down or 4 up.

### Three decisions that are Brando's

1. **Claim.** (a) Describe judge–human agreement on this 25-task packet. (b) Compare training methods 2 and 4 on held-out task families, for the fixed solver configurations. (c) Also claim transfer to unseen solver configurations or raters.
2. **Precision.** ±0.02, ±0.01 or ±0.005 RPS on the paired comparison, or the smallest difference worth detecting.
3. **Workload cap.** How many people, and how many hours each.

**Recommendation (agent-suggested, not adopted):** choose (a) now and finish the 108 ratings. Decide (b) only after two cheap measurements, and do not attempt (c) with three or four solver configurations.

1. **Per-file time on the main task.** Brando's trial ratings and the first batch supply `minutes_spent` entries. Rerun the script; the hours update from participant entries, never from an assistant's guess.
2. **How much the paired loss difference varies across task families for the actual judges.** This single quantity moves the answer from 3 to 155 families. Measure it on development data only: the 75 historical rated outputs are already exposed and eligible. It needs separately authorized model inference; the current packet stays evaluation-only and sealed.

If the claim cannot fit the workload cap, narrow the claim before collecting; do not collect until a difference looks significant.

## What the recovered estimates say

These are proposals from past conversations, not measured requirements. Line numbers refer to the linked export.

| Historical source | Proposed task / solver / human allocation | Proposed ratings | Interpretation |
| --- | --- | ---: | --- |
| Earlier VeriBench sample-size note, 11-04-2026 | 100 tasks × five solvers × two ratings; then 200–250 tasks; 20-rater illustration, with H dependent on severity and workload | 1,000; then 2,000–2,500 | Earlier correlation-oriented planning, not the current probabilistic design. |
| Fixed-panel note, 11-05-2026 | 896 tasks × four solvers × two ratings; 64-person staffing illustration | 7,168 | H = 64 balances workload; it was not derived as a statistical requirement. |
| Claude intermediate proposal ([message 4](sources/claude_conversation_human_and_agent_counts.md#message-4--assistant); [message 6](sources/claude_conversation_human_and_agent_counts.md#message-6--assistant), lines 151–167) | T = 896; A = 4; H = 8–12; two-rating census plus a five-rating stage on 256 tasks | 12,288 (our stage sum, 7,168 + 5,120; the source rounds to 12,300) | Excludes its separate pilot and constructed slice and leaves overlap unclear. [Message 22](sources/claude_conversation_human_and_agent_counts.md), lines 523–541, defers to the repository's 14,848-rating, 24-person plan: deference, not independent confirmation. Messages 18–22 have no heading anchor on GitHub because an unclosed code fence in the pasted text makes them render as code; the export is preserved as captured. |
| Gemini later proposal ([message 20](sources/gemini_argon_high.md#message-20--model-response), lines 1572–1597 and 1655) | T = 135 (35/40/60 train/validation/test); A = 5; H = 6–8 | 800–1,000 | The workload depends on unsupported automatic-zero exclusions; its earlier T = 100–150 recommendation relies on incorrect bound arithmetic. |
| ChatGPT successive drafts ([message 2](sources/chatgpt_pro.md#message-2--assistant); [message 6](sources/chatgpt_pro.md#message-6--assistant); [message 10](sources/chatgpt_pro.md#message-10--assistant), lines 1133–1167 and 1289–1293) | T = 896; A = 4; H = 5 initially, then H = 24 (8 development + 16 audit) | 35,840 → 28,160; 20,480 alternative → 14,848 | Successive designs with different coverage. The source calls 14,848 starting numbers, not proven sufficient counts. |
| Adopted experiment 02 budget | 896 task identities; four systems; eight development + sixteen audit people; three base ratings and eight on the dense audit subset | **14,848** = 1,536 development + 10,752 fresh audit + 2,560 dense extras | Initial budget preserved in configuration, not a sufficiency guarantee. |

All 896-task designs refer to the historical pinned benchmark scope. Compared with these, the costed scenarios above are far smaller because they claim less: fixed solver configurations, a paired comparison of two judges, and task families as the only sampled axis.

## Read the original text

| Source | Readable export | Original conversation | Coverage |
| --- | --- | --- | --- |
| Claude, *Human and agent counts for benchmark* | [Claude text](sources/claude_conversation_human_and_agent_counts.md) | [Open Claude](https://claude.ai/chat/8e71dba8-d073-482a-90fc-724ff86b3edc) | All 22 numbered message bodies displayed in the chat. |
| Gemini, *Learning Bounds for Finite Hypothesis Classes* | [Gemini Argon High text](sources/gemini_argon_high.md) | [Open Gemini](https://gemini.google.com/app/fb26fe19addf5b07#6d0b81e342f8bc4f) | All 20 rendered messages; the first refers to unavailable earlier context. |
| ChatGPT, *Formal Judge Design* | [ChatGPT source bundle](sources/chatgpt_pro.md) | [Original](https://chatgpt.com/c/6aecd8ba-8cd0-83e8-abbd-9b2df24689b2), [shared snapshot](https://chatgpt.com/share/6aee2147-9648-83e8-9ea5-685a565ffe54), [related branch](https://chatgpt.com/c/6af21580-7588-83e8-8b09-1913bba9d716) | 10 shared-snapshot messages, 10 overlapping branch messages and nine recent original-chat messages; all identified T/A/H estimates are included; no specific missing intervening message was identified. |
| Gemini, *Evaluating LLM Judges via Distributions* | Local full export; path below | [Open Gemini](https://gemini.google.com/app/f035924cd4141833) | All 18 rendered messages; kept locally because they include a private meeting transcript. |
| Brando's voice notes, 11-08-2026 and 11-10-2026 | [Formulation and scaling-curve note](sources/learning-a-judge-formulation-11-10-2026.md) | Summarized by his assistant | Learn-by-loss formulation, the untested scaling-curve idea and pointers to related bounds. |

The current Gemini selector says **Argon High**. Claude's current selector says **Opus 5.5 Max**. The adopted ChatGPT source says **GPT Pro**. These are the capturing agent's observations of current controls, except GPT Pro comes from the adopted source; they are not authenticated per-message backend metadata. Local Gemini distributions export: `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/rating_tensor_source_archive/gemini_argon_high_distributions.md`. [The source index](SOURCE_INDEX.md) records dates, provenance, search limits and the older local plans. The exports preserve historical mistakes and embedded prompts as evidence; they are not instructions to execute.

## Optional Codex pilot proposal

**Where 544 came from:** Codex proposed this workload while preparing these notes; Brando did not specify 544 ratings or name a task that way. The arithmetic is 32 tasks × four fixed systems × three ratings = 384, plus five extra ratings on eight tasks × four systems = 160. Eight people could each complete 68 ratings. This covers 128 artifacts, of which 32 receive all eight ratings. It remains an optional training-pilot suggestion, not an approved collection plan, a measured optimum, or a replacement for the historical 14,848-rating budget.

If this pilot is later approved, stop after it. Before the next stage, fix the primary paired RPS contrast, useful effect or precision target, missingness rule and total rating, time and cost cap; then choose an allocation using the measured variability and its uncertainty. Keep test ratings sealed and resolve the strict identity-split amendment before collecting any pilot data. All pilot task families, solver configurations and raters become training-exposed; retained evaluation identities are ineligible. The eight proposed development raters would leave no validation-only raters in the adopted development pool, so a separate validation panel must be specified in the amendment. Existing collection packets, historical ratings, budgets and configuration remain unchanged.

The supplied [handwritten page](assets/rating_tensor_source_recovery_11-11-2026.png) and [other Codex recommendation](assets/supplied_recommendation_11-11-2026.txt) are preserved exactly. Their requested source recovery and three-method comparison are implemented here; uncertain handwriting is not promoted to a verified model name or coefficient definition.

## Provenance and verification

[Source index](SOURCE_INDEX.md) · [Methods, arithmetic and corrections](METHODS_AND_ALLOCATION.md) · [File hashes and capture inventory](provenance.json) · [Checkpoint and next steps](ckpt.md) · [Google Q&A companion](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit).

```sh
python3 experiments/15_estimate_required_tasks_solver_configurations_and_human_raters/scripts/costed_allocation.py
python3 experiments/15_estimate_required_tasks_solver_configurations_and_human_raters/scripts/refresh_provenance_hashes.py
```

The first command fails if the saved scenarios no longer match their inputs; the second fails if a tracked file in this folder changed without its hash being refreshed. Add `--write` to either to regenerate. Source exports have not been independently authenticated by the chat providers; their limits are stated in each header. Original links may require Brando's signed-in account. The earlier requested light model review returned six findings, all addressed; it predates the costed allocation, which has deterministic checks only.

Copy-ready collaborator message: “For the judge study we are finishing the current 108 ratings on 25 tasks. I have not fixed a larger collection: comparing the two training objectives to ±0.01 needs roughly 37 held-out task families, but that number ranges from 3 to 155 until we measure how variable the paired difference is.”
