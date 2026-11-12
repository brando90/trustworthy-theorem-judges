# AI assistance and reference problems in human ratings

**Doc link:** <https://github.com/brando90/veribench/blob/main/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml/human_round/AI_ASSISTANCE_POLICY.md>

**TLDR:** Localized Lean questions are allowed; each person must make the final rating. Rate reasonable conventions with your own judgment; report only references that are actually incorrect (paragraph updated 10-11-2026).

## Policy effective 10-10-2026

You may ask an artificial intelligence (AI) tool a localized question about Lean syntax, notation, types or library behavior, using only the small snippet needed to explain the question. For example: “What does `∀ x, P x → Q x` mean?” or “How does list indexing work in Lean?”

Do not upload or paste a complete reference or agent Lean file, a whole task folder, or a sequence of snippets that reconstructs one. Do not ask a model to perform the rating task: comparing an agent with the reference, deciding which properties are covered, proposing a score, or writing your rating rationale. The final comparison, score and rationale must be your own. Review an explanation critically; a model answer is not evidence that the code is correct.

Rate independently, keep the system identities and other people's ratings hidden, and do not discuss particular items with other raters before the round closes. If you use a tool, briefly note the kind of localized help in `problem_note`; do not paste private conversations or model-generated ratings into the sheet.

Specifications of real code are often ambiguous, for example what to return on an empty list when the Python raises an error. When a reference picks a reasonable convention for such a case, rate with your own judgment and note your reasoning in `rationale`; some variation between raters is expected. Only if something is actually incorrect (a reference theorem that is false, or one that contradicts the Python on an input the Python accepts) put the smallest concrete example in `problem_note`, leave that score blank and email brandojazz@gmail.com. Every reference was checked on 10-11-2026, so we don't expect this.

This replaces the blanket “no AI tools” rule in the recruitment email and packet wrappers. The original May scoring rubric, score scale, blind ordering, candidate files and reference files are unchanged. The old and newly clarified assistance conditions must be distinguished in the collection record.

## Why the policy changed

Brando reaffirmed this choice on 10-10-2026 and asked that its implications for training, evaluation and the paper be recorded. The purpose is to support technical comprehension with localized Lean help while retaining human responsibility for comparisons, scores and rationales. Tool access is permitted, not required.

This changes the rating-collection procedure and may change the resulting ratings. It does not change the intended coverage question or scoring rubric. Realism is a motivation, not evidence of better accuracy, unchanged ratings, universal tool use, or successful compliance with either policy. A human's final decision can still be influenced by a model's explanation, including in ways correlated with an automated judge.

## Collection record and use of the ratings

These are intake and reporting requirements, not a claim that existing ratings have already been tagged or that assistance effects have been measured. Keep the original submissions intact and attach collection metadata separately. Continue using `problem_note` for the requested brief assistance description; a blank note means use is unknown, not that no tool was used.

| Record | Required interpretation |
|---|---|
| Assistance policy received | `no_ai_instructed`, `localized_ai_permitted`, or `unknown`; retain the instruction version and evidence of when the rater received or acknowledged it. |
| Reported assistance | `reported_no_use`, `localized_help_reported`, `outside_policy_reported`, or `unknown`; distinguish an explicit report of no use from silence. |
| Assistance description | Kind of help and tool/model if the rater supplies them; unknown remains unknown. Full private conversations are unnecessary. |
| Rating identity and timing | Rater identifier, item identifier, rating time if known, and submission time; a late submission can contain ratings made under earlier instructions. |
| Task version | Exact packet listing and Python, reference Lean, candidate Lean and rubric hashes; a rating is bound to the reference as well as the candidate. |
| Prior exposure and split | Task family, previous use for training or selection, and the frozen analysis role. New ratings or candidates on an exposed task do not create an unseen task. |

Record the policy actually applicable to each rating when possible. Preserve mixed or unresolved sessions explicitly; the date an email was sent is not evidence that every recipient had read it. Do not infer compliance, impute assistance, discard ratings, or move them between splits based on the score.

Older ratings may be reused for future training or judge selection under a new recorded condition, after checking task validity and training/evaluation overlap. Such reuse does not erase their original split or restore their independence as a test of the updated judge. Reference problems do not become harmless merely because ratings are used for training.

Reserve incoming ratings for the already specified evaluation of the frozen judge. If those ratings later inform a prompt, model, score mapping or threshold, record that use as training or validation as appropriate and evaluate the revised judge on a separate held-out set. Define separation by underlying task families and prior exposure, not just by row or candidate filename. Both packets were released on 10-11-2026 after the reference corrections in [experiment 114](../../114_fix_rylans_detected_bugs_human_rating_packet/README.md).

Report collection conditions distinctly. Any pooled result must identify its mixed assistance and task-version conditions; it is not an estimate for unaided humans alone. Where metadata and sample sizes permit, report descriptive sensitivity analyses by policy and reported use, retaining an unknown group. Self-selected tool use and before/after comparisons cannot by themselves identify a causal assistance effect. This note changes no frozen primary analysis, threshold or historical result; any new analysis must be specified before reading scores and identified separately.

The paper records the rationale and limitations in `paper_latex/TMLR_2026_VeriBench/98_5_appendix_human_judgement_collection.tex`. This policy is consistent with documenting collection procedures and intended uses in [Datasheets for Datasets](https://arxiv.org/abs/1803.09010). [Veselovsky, Horta Ribeiro and West](https://arxiv.org/abs/2306.07899) studied tool use in crowd-worker summarization; their findings do not establish its prevalence or effects among our Lean raters.
