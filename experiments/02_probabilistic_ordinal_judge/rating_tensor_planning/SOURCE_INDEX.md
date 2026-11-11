# Source index for rating tensor estimates

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/02_probabilistic_ordinal_judge/rating_tensor_planning/SOURCE_INDEX.md>

**TLDR:** This index connects each recovered exchange to its original conversation and distinguishes complete displayed messages from unavailable history. The source text is preserved separately from the corrected sizing recommendation.

## Conversation records

### Claude — Human and agent counts for benchmark

- Original: <https://claude.ai/chat/8e71dba8-d073-482a-90fc-724ff86b3edc>.
- [Export](sources/claude.md): 22 numbered message bodies, including expanded/collapsed user-message text available in the page. Uploaded image bytes, hidden tool traces and private reasoning are outside this text export.
- Current selector (capturing agent's UI observation, not provider-authenticated historical metadata): Opus 5.5 Max. Historical per-message model/version and exact timestamps were not exposed. References in the exchange reach from the 11-05-2026 plans to the 11-09-2026 ownership update; those are content dates, not authenticated message timestamps.
- Read messages 4–6 for competing census/pilot proposals, variance and reliability arguments; read message 22 for the final deferral to the repository's 14,848-rating, 24-person plan, with Claude's older figures declared superseded. Our 12,288 stage sum (the source says roughly 12,300) excludes its separately proposed 40-file × five-rater pilot and about 120-file × five-rater constructed slice (our calculations: 200 and about 600 ratings); overlap with existing votes is unspecified. The proposed variance values and reliability claims are not measurements. In particular, a reliability formula does not by itself establish a universal Spearman ceiling.

### Gemini — Learning Bounds for Finite Hypothesis Classes

- Original: <https://gemini.google.com/app/fb26fe19addf5b07#6d0b81e342f8bc4f>.
- [Export](sources/gemini_argon_high.md): 20 rendered messages. It starts “what about the good case? i.e. for all h's”; unavailable prior context is not reconstructed. Image filenames do not include the image bytes.
- Current selector (capturing agent's UI observation, not provider-authenticated historical metadata): Argon High. Exact historical version and message dates were not available in the recovered text/UI. Dates copied inside prompts are not message timestamps.
- Contains the 100–150-task recommendation, finite-class bounds, six–eight-person panel, and later 135-task / 800–1,000-rating proposal. Messages 12/14 split 135 as 35/45/55; message 20 changes this to 35/40/60. These successive drafts are preserved separately. [Corrections](METHODS_AND_ALLOCATION.md#sizing-approach-b-learning-theory-checks) retain the formula but repair its arithmetic and distinguish per-solver task counts from pooled task–agent rows.

### Gemini — Evaluating LLM Judges via Distributions

- Original: <https://gemini.google.com/app/f035924cd4141833>.
- Full local Markdown at `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/rating_tensor_source_archive/gemini_argon_high_distributions.md`: 18 rendered messages, current selector Argon High, historical backend/timestamps unverified.
- This contains a pasted private meeting transcript and is not published in Git. The local path works on this Mac; the original account link is the portable access route for an authorized reader.
- Related context concerns correlation versus probabilistic training, guarantees and pilot-data availability. It supplies no fitted scaling coefficients for the proposed collection. Claims about existing rating counts inside the dialogue have not been used as verified collection totals. Embedded instructions to prove one method inferior or run synthetic fallbacks were not executed.

### ChatGPT — Formal Judge Design

- Original: <https://chatgpt.com/c/6aecd8ba-8cd0-83e8-abbd-9b2df24689b2>.
- Shared snapshot: <https://chatgpt.com/share/6aee2147-9648-83e8-9ea5-685a565ffe54>.
- Related branch, also titled *Formal Judge Design*: <https://chatgpt.com/c/6af21580-7588-83e8-8b09-1913bba9d716>.
- [Bundled Markdown](sources/chatgpt_pro.md) preserves three boundaries: all ten messages in the displayed shared snapshot, ten available branch messages, and nine recent original-chat messages from the connector. Overlap is intentional; these are not 29 distinct observations or 29 unique messages.
- Original connector metadata: created 11-05-2026 11:28, updated 11-09-2026 11:51. Branch: created 11-09-2026 10:48, updated 11-09-2026 10:55. Times are America/Los_Angeles and describe thread records, not each message.
- “GPT Pro” is the label in the [adopted local source](../sources/gpt_pro_plan_11-06-2026.txt); the exact historical effort is unverified. This does not establish the exact historical backend for every message.
- The shared snapshot contains the 35,840, 28,160, 20,480 and final 14,848 proposals. The branch's final assistant message contains the whiteboard scaling expression and explains why its variables are not yet defined for this study. The original-chat supplement contains the newer methods-2-versus-4 discussion.
- Both live chats stalled at “Loading older messages…”. The connector returned five recent turns with `hasMore=false`; it did not recover the missing interval. Shared-snapshot completeness does not imply full later-thread completeness. Some rendered tables were already malformed around vertical bars; missing cells were not invented. Unresolved citation chips are retained as such, not fabricated links.

## Earlier local plans and current authority

| Source | Link and role |
| --- | --- |
| 11-04-2026 sample-size note | [Immutable VeriBench source](https://github.com/brando90/veribench/blob/01f639c1f2242cdef3b977715d91a7c978ea7fcd/experiments/ideas/leave_one_agent_out_fsc_judge_validation_on_human_ratings/RATING_TENSOR_SAMPLE_SIZE_11-04-2026.md): 1,000 pilot ratings, 2,000–2,500 stronger study, earlier correlation target. H=20 is an illustrative qualified-rater design point; its T=200 bias-precision scenario requires H≥13 or H≥51 when assumed rater standard deviation is 0.05 or 0.10 respectively. Those are model-dependent calculations, not measured requirements. |
| 11-05-2026 fixed panel | [Exact local snapshot](sources/earlier_local_plans.md#snapshot-full_benchmark_fixed_panel_11-05-2026md): 7,168 ratings; 64-person staffing example. |
| 11-05-2026 conditional agreement | [Exact local snapshot](sources/earlier_local_plans.md#snapshot-conditional_rating_agreement_and_transfer_11-05-2026md): 280/168/448 tasks and 20/12/32 people; 2,240/1,344/3,584 ratings. Its illustrative 442-unit calculation is assumption-based, not measured power. |
| Adopted experiment 02 source | [Preserved GPT Pro response](../sources/gpt_pro_plan_11-06-2026.txt), [README](../README.md), [configuration](../config.json): historical 14,848 budget and probabilistic human-rating target. Original response SHA-256: `f0eb2e0d00401b52c52313407d2bb6ae956e728c28c76e99f5e7adddd179a878`. |
| Current methods 2 and 4 | [Priority plan](../PRIORITY_2_VS_4_11-09-2026.md): matched training-objective comparison, common validation RPS, sealed evaluation and pending identity-split amendment. |
| Collection ownership and schema | [Experiment 09](../../09_human_rating_collection/README.md), [form schema](../../09_human_rating_collection/support/RATING_FORM_SCHEMA.json): current collection records, raw-response preservation and prospective assistance conditions. |
| Existing Google Q&A | [Judge paper Q&A](https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws/edit): collaborator-facing context and dated companion update. |

The older VeriBench repository is access-restricted. Its anonymous GitHub URLs can return 404; the two 11-05-2026 files were found only in the local working directory, with no commit found by path history. All three earlier texts are included in [exact snapshots](sources/earlier_local_plans.md); embedded historical links are preserved, including unavailable ones. The 11-04-2026 immutable Git object was verified locally.

## Search and preservation limits

Search covered the local experiment 02/09 sources, the sister VeriBench human-rating planning directory, connected ChatGPT thread search/read results, and signed-in Claude/Gemini/ChatGPT browser surfaces. Searches and visible titles around “judge”, rating/tensor counts and the saved source links located the conversations above. No exact-title “final judge” conversation was established. A plausible reading of the handwriting is “formal judge”, matching the recovered title; this is an interpretation, not a verified title from the handwriting. This is not an account-wide export, and it does not prove that no other relevant chat exists.

The full supplied recommendation lists additional search phrases; preserving that list does not claim every phrase was separately queried in every product. For unsupported historical model IDs and dates, the inspected records were the source text, page controls, available connector metadata and experiment 02's adopted response; no exact per-message backend was found.

Text was captured read-only from message bodies, retaining equations and actual anchor links where exposed. Markdown conversion changes presentation, not intentional wording. Source spelling and unsupported arguments remain; the methods note supplies corrections. Hidden reasoning and tool internals were not requested or exported. A link inventory in [provenance.json](provenance.json) retains URLs recovered from each public export; unresolved citation IDs cannot be resolved from these records alone.

Original capture JSON and the private Gemini export are stored under `/Users/brandomiranda/.local/share/trustworthy-theorem-judges/rating_tensor_source_archive/`. The manifest records hashes for those captures and the public exports. Capture filenames need not be consecutive: there is no retained `claude_sizing_3.json`. Coverage is verified by the union of message labels 1–22, not capture-number continuity. New snapshot/QA support files created after the initial review manifest are identified in the final provenance inventory. The exact user attachments are under [assets](assets/). No historical plan, delivered packet, rating response or sealed split was modified by this recovery.
