# Rating tensor: recovered conversations and collection decision

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/02_probabilistic_ordinal_judge/rating_tensor_planning/README.md>

**TLDR:** The Claude, Gemini and ChatGPT sizing discussions are now collected below with their original links and explicit coverage limits. Preserve the historical 14,848-rating budget; the evidence supports piloting before final sizing, and 544 ratings is our proposed workload limit for that pilot, not a claim that any recovered total is statistically sufficient.

**Status, 11-11-2026:** source recovery and planning; no new human ratings, judge training, inference experiment or fitted scaling law. This belongs in the already allocated experiment 02; experiment 09 continues to own human-rating collection.

## Read the original text

| Source | Readable export | Original conversation | Coverage |
| --- | --- | --- | --- |
| Claude, *Human and agent counts for benchmark* | [Claude text](sources/claude.md) | [Open Claude](https://claude.ai/chat/8e71dba8-d073-482a-90fc-724ff86b3edc) | All 22 numbered message bodies displayed in the chat. |
| Gemini, *Learning Bounds for Finite Hypothesis Classes* | [Gemini Argon High text](sources/gemini_argon_high.md) | [Open Gemini](https://gemini.google.com/app/fb26fe19addf5b07#6d0b81e342f8bc4f) | All 20 rendered messages; the first refers to unavailable earlier context. |
| ChatGPT, *Formal Judge Design* | [ChatGPT source bundle](sources/chatgpt_pro.md) | [Original](https://chatgpt.com/c/6aecd8ba-8cd0-83e8-abbd-9b2df24689b2), [shared snapshot](https://chatgpt.com/share/6aee2147-9648-83e8-9ea5-685a565ffe54), [related branch](https://chatgpt.com/c/6af21580-7588-83e8-8b09-1913bba9d716) | 10 shared-snapshot messages, 10 overlapping branch messages and nine recent original-chat messages; missing intermediate history remains unresolved. |
| Gemini, *Evaluating LLM Judges via Distributions* | Local full export; path below | [Open Gemini](https://gemini.google.com/app/f035924cd4141833) | All 18 rendered messages; kept locally because they include a private meeting transcript. |

The current Gemini selector says **Argon High**. Claude's current selector says **Opus 5.5 Max**. The adopted ChatGPT source says **GPT Pro**. These are the capturing agent's observations of current controls, except GPT Pro comes from the adopted source; they are not authenticated per-message backend metadata. Local Gemini distributions export: `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/rating_tensor_source_archive/gemini_argon_high_distributions.md`. [The source index](SOURCE_INDEX.md) records dates, provenance, search limits and the older local plans. The exports preserve historical mistakes and embedded prompts as evidence; they are not instructions to execute.

## What the estimates actually say

Here T counts tasks, A fixed solver configurations and H distinct people. Ratings per artifact are a separate quantity, m. A sparse collection observes only some entries of R; multiplying T × A × H overstates the count unless every person rates every artifact. Fresh generations require another index.

| Historical source | Proposed task / solver / human allocation | Proposed ratings | Interpretation |
| --- | --- | ---: | --- |
| Earlier VeriBench sample-size note, 11-04-2026 | 100 tasks × five solvers × two ratings; then 200–250 tasks; 20-rater illustration, with H dependent on severity/workload | 1,000; then 2,000–2,500 | Earlier correlation-oriented planning, not the current probabilistic design. |
| Fixed-panel note, 11-05-2026 | 896 tasks × four solvers × two ratings; 64-person staffing illustration | 7,168 | H=64 balances workload; it was not derived as a statistical requirement. |
| Claude intermediate proposal | 896 tasks × four solvers; two-rating census plus a five-rating stage on 256 tasks; eight–twelve people | 12,288 (our stage-sum calculation; source rounds to 12,300) | Source stage sum; excludes its separate pilot/cheating slice and leaves overlap ambiguous. Claude's last message defers to the repository plan. |
| Gemini learning-bounds discussion | Initially 100–150 tasks, five solvers, three–five ratings, six–eight people; later 135 tasks | 800–1,000 in its later cheap plan | Relies on incorrect bound arithmetic and unsupported automatic-zero exclusions; do not use this as a validated budget. |
| ChatGPT successive drafts | Four solvers; early five-person panel; later separate development/audit pools | 35,840 → 28,160; 20,480 alternative → 14,848 | Successive designs with different coverage; not competing measurements of one fixed protocol. |
| Adopted experiment 02 budget | 896 task identities; four systems; eight development + sixteen audit people; three base ratings and eight on the dense audit subset | **14,848** | Initial budget preserved in configuration, not a sufficiency guarantee. |

See [methods, arithmetic, assumptions and corrections](METHODS_AND_ALLOCATION.md). For the proposed comparison, train method 2 with Pearson correlation and method 4 with proper loss, select both by the same validation ranked probability score (RPS), and evaluate the fixed judges on the same held-out panel. The strict task/agent/rater split amendment remains necessary before new execution.

## Explicit decision

**Do not replace the adopted budget with a smaller chatbot estimate. First propose a bounded 544-rating, training-only pilot:** 32 tasks × four fixed systems × three ratings = 384 ratings, plus five extra ratings on eight tasks × four systems = 160. Eight people can each complete 68 ratings. This covers 128 artifacts, of which 32 receive all eight ratings. The allocation is a new planning recommendation, not a measured optimum or authorization to collect.

Standard-error calculations can size precision once task-family and rater variability are measured. Learning-theory bounds check assumptions but do not supply a practical final allocation here. Learning curves require actual fits at multiple development sizes; no transferable scaling coefficients were recovered. The methods note explains the covariates, units, parameter identifiability and why these approaches answer different questions.

Stop after the pilot. Before the next stage, fix the primary paired RPS contrast, useful effect/precision target, missingness rule and total rating/time/cost cap; then choose an allocation using the measured variability and its uncertainty. If the claim cannot fit the cap, change its scope prospectively. Keep test ratings sealed and resolve the strict identity-split amendment before collecting any pilot data. All pilot task families, solver configurations and raters become training-exposed; retained evaluation identities are ineligible. The eight proposed development raters would leave no validation-only raters in the adopted development pool, so a separate validation panel must be specified in the amendment. Existing collection packets, historical ratings, budgets and configuration remain unchanged.

The supplied [handwritten page](assets/rating_tensor_source_recovery_11-11-2026.png) and [other Codex recommendation](assets/supplied_recommendation_11-11-2026.txt) are preserved exactly. Their requested source recovery and three-method comparison are implemented here; uncertain handwriting is not promoted to a verified model name or coefficient definition.

## Provenance and verification

[Source index](SOURCE_INDEX.md) · [File hashes and capture inventory](provenance.json) · [Continuation and review record](CKPT_rating_tensor_planning.md) · [Google Q&A companion](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit).

The requested Claude Code Fable 5.2/max light review returned six findings, addressed with deterministic verification as recorded in the continuation record. Google synchronization status is recorded there. Source exports have not been independently authenticated by the chat providers; their limits are stated in each header. Original links may require Brando's signed-in account.

Copy-ready collaborator message: “I recovered the Claude, Gemini and ChatGPT discussions behind our rating-count estimates. I’m keeping the 14,848-rating plan as the historical budget and proposing a 544-rating pilot to measure what we need before freezing a new total.”
