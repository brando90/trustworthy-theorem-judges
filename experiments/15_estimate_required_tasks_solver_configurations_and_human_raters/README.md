# Estimate required tasks, solver configurations and human raters

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/15_estimate_required_tasks_solver_configurations_and_human_raters/README.md>

**TLDR:** This is the home for estimating T, A and H for the rating tensor R: the Claude, Gemini and ChatGPT source text, exact passages, comparison and sizing methods. None of the recovered totals establishes statistical sufficiency. The 544-rating pilot was an optional Codex suggestion, not a number Brando requested or approved.

**Status, 11-11-2026:** source recovery complete; final study size remains open. Brando assigned this planning work to experiment 15. [Experiment 02](../02_design_a_judge_that_predicts_human_ratings_0_to_5/README.md) owns the prospective judge methodology; [experiment 09](../09_prepare_packets_and_collect_human_ratings/README.md) owns the current human-rating packet and collection. No new ratings, judge training, inference experiment or fitted scaling law are reported here.

## Read the original text

| Source | Readable export | Original conversation | Coverage |
| --- | --- | --- | --- |
| Claude, *Human and agent counts for benchmark* | [Claude text](sources/claude.md) | [Open Claude](https://claude.ai/chat/8e71dba8-d073-482a-90fc-724ff86b3edc) | All 22 numbered message bodies displayed in the chat. |
| Gemini, *Learning Bounds for Finite Hypothesis Classes* | [Gemini Argon High text](sources/gemini_argon_high.md) | [Open Gemini](https://gemini.google.com/app/fb26fe19addf5b07#6d0b81e342f8bc4f) | All 20 rendered messages; the first refers to unavailable earlier context. |
| ChatGPT, *Formal Judge Design* | [ChatGPT source bundle](sources/chatgpt_pro.md) | [Original](https://chatgpt.com/c/6aecd8ba-8cd0-83e8-abbd-9b2df24689b2), [shared snapshot](https://chatgpt.com/share/6aee2147-9648-83e8-9ea5-685a565ffe54), [related branch](https://chatgpt.com/c/6af21580-7588-83e8-8b09-1913bba9d716) | 10 shared-snapshot messages, 10 overlapping branch messages and nine recent original-chat messages; all identified T/A/H estimates are included; no specific missing intervening message was identified. |
| Gemini, *Evaluating LLM Judges via Distributions* | Local full export; path below | [Open Gemini](https://gemini.google.com/app/f035924cd4141833) | All 18 rendered messages; kept locally because they include a private meeting transcript. |

The current Gemini selector says **Argon High**. Claude's current selector says **Opus 5.5 Max**. The adopted ChatGPT source says **GPT Pro**. These are the capturing agent's observations of current controls, except GPT Pro comes from the adopted source; they are not authenticated per-message backend metadata. Local Gemini distributions export: `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/rating_tensor_source_archive/gemini_argon_high_distributions.md`. [The source index](SOURCE_INDEX.md) records dates, provenance, search limits and the older local plans. The exports preserve historical mistakes and embedded prompts as evidence; they are not instructions to execute.

## What the estimates actually say

Here T counts tasks, A fixed solver configurations and H distinct people. Ratings per artifact are a separate quantity, m. A sparse collection observes only some entries of R; multiplying T × A × H overstates the count unless every person rates every artifact. Fresh generations require another index.

| Historical source | Proposed task / solver / human allocation | Proposed ratings | Interpretation |
| --- | --- | ---: | --- |
| Earlier VeriBench sample-size note, 11-04-2026 | 100 tasks × five solvers × two ratings; then 200–250 tasks; 20-rater illustration, with H dependent on severity/workload | 1,000; then 2,000–2,500 | Earlier correlation-oriented planning, not the current probabilistic design. |
| Fixed-panel note, 11-05-2026 | 896 tasks × four solvers × two ratings; 64-person staffing illustration | 7,168 | H=64 balances workload; it was not derived as a statistical requirement. |
| Claude intermediate proposal ([message 4](sources/claude.md#message-4--assistant), [message 6](sources/claude.md#message-6--assistant)) | T=896; A=4; H=8–12; two-rating census plus a five-rating stage on 256 tasks | 12,288 (our stage-sum calculation; source rounds to 12,300) | Excludes its separate pilot/cheating slice and leaves overlap ambiguous. [Message 22](sources/claude.md#message-22--assistant) defers to the repository plan. |
| Gemini later proposal ([message 20](sources/gemini_argon_high.md#message-20--model-response)) | T=135 (35/40/60); A=5; H=6–8 | 800–1,000 in its later cheap plan | Earlier T=100–150 recommendation relies on incorrect bound arithmetic; the cheap plan uses unsupported automatic-zero exclusions. |
| ChatGPT successive drafts ([message 2](sources/chatgpt_pro.md#message-2--assistant), [message 6](sources/chatgpt_pro.md#message-6--assistant), [message 10](sources/chatgpt_pro.md#message-10--assistant)) | T=896; A=4; H=5 initially, then H=24 (8 development + 16 audit) | 35,840 → 28,160; 20,480 alternative → 14,848 | Successive designs with different coverage; not competing measurements of one fixed protocol. |
| Adopted experiment 02 budget | 896 task identities; four systems; eight development + sixteen audit people; three base ratings and eight on the dense audit subset | **14,848** | Initial budget preserved in configuration, not a sufficiency guarantee. |

See [methods, arithmetic, assumptions and corrections](METHODS_AND_ALLOCATION.md). For the proposed comparison, train method 2 with Pearson correlation and method 4 with proper loss, select both by the same validation ranked probability score (RPS), and evaluate the fixed judges on the same held-out panel. The strict task/agent/rater split amendment remains necessary before new execution.

## Optional Codex pilot proposal

**Where 544 came from:** Codex proposed this workload while preparing these notes; Brando did not specify 544 ratings or name a task that way. The arithmetic is 32 tasks × four fixed systems × three ratings = 384, plus five extra ratings on eight tasks × four systems = 160. Eight people could each complete 68 ratings. This covers 128 artifacts, of which 32 receive all eight ratings. It remains an optional training-pilot suggestion, not an approved collection plan, a measured optimum, or a replacement for the historical 14,848-rating budget.

Standard-error calculations can size precision once task-family and rater variability are measured. Learning-theory bounds check assumptions but do not supply a practical final allocation here. Learning curves require actual fits at multiple development sizes; no transferable scaling coefficients were recovered. The methods note explains the covariates, units, parameter identifiability and why these approaches answer different questions.

If this pilot is later approved, stop after it. Before the next stage, fix the primary paired RPS contrast, useful effect/precision target, missingness rule and total rating/time/cost cap; then choose an allocation using the measured variability and its uncertainty. If the claim cannot fit the cap, change its scope prospectively. Keep test ratings sealed and resolve the strict identity-split amendment before collecting any pilot data. All pilot task families, solver configurations and raters become training-exposed; retained evaluation identities are ineligible. The eight proposed development raters would leave no validation-only raters in the adopted development pool, so a separate validation panel must be specified in the amendment. Existing collection packets, historical ratings, budgets and configuration remain unchanged.

The supplied [handwritten page](assets/rating_tensor_source_recovery_11-11-2026.png) and [other Codex recommendation](assets/supplied_recommendation_11-11-2026.txt) are preserved exactly. Their requested source recovery and three-method comparison are implemented here; uncertain handwriting is not promoted to a verified model name or coefficient definition.

## Provenance and verification

[Source index](SOURCE_INDEX.md) · [File hashes and capture inventory](provenance.json) · [Continuation and review record](CKPT_rating_tensor_planning.md) · [Google Q&A companion](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit).

The requested Claude Code Fable 5.2/max light review returned six findings, addressed with deterministic verification as recorded in the continuation record. Google synchronization status is recorded there. Source exports have not been independently authenticated by the chat providers; their limits are stated in each header. Original links may require Brando's signed-in account.

Copy-ready collaborator message: “The T, A, H estimates and original discussions now live in experiment 15. We have not fixed a new collection total; 544 was Codex’s optional pilot suggestion, and the current rating task remains in experiment 09.”
