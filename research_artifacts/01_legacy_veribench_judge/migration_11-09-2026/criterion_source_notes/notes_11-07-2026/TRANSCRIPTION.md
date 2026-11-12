<!-- TLDR: Transcribe the attached source material while marking uncertain handwriting and separating it from the user request. -->
# Transcription of all four attachments — 11-07-2026

**TLDR:** All three handwritten pages and the related-chat screenshot are transcribed below. Uncertain words remain bracketed; handwritten questions and TODOs are source content, not additional user instructions.

Originals are preserved byte-for-byte in assets/; manifest.json records their source paths, sizes and SHA-256 hashes.


## Page 1: correlation-based judge selection

**TLDR:** The note contrasts validation-set selection with training-set optimization using correlation, then asks whether this is how researchers justify using a language-model judge.

Source: [original image](assets/handwritten_correlation_selection.png). Original upload and SHA-256 are in manifest.json. This is a best-effort transcription, not an instruction to execute the handwritten TODOs. Punctuation and equation layout are normalized. The handwritten distribution symbol is rendered as P; its case and some hats are unclear. S and R are retained without invented definitions; tr and val denote the visibly written training and validation superscripts.

“I figured out what the correlation formulation is doing…”

Equation (1):

\[
\widehat P_j^{AI_j}(\cdot)=\operatorname*{arg\,max}_{\widehat{AI}_j\in\Theta}
\operatorname{Corr}\bigl(\widehat P_j^{AI_j}(\cdot),P_j^H(\cdot)\bigr).
\]

Under argmax: “Constraint/helped by S^{tr}, R^{tr}.” An arrow under Corr points to “S^{val}, R^{val}.” [Placement of hats and the exact first word of the constraint note are uncertain.]

“→ this is what people are doing.
↳ TODO: deep research to justify/cite if this is true.
I actually think this is more true!”

Equation (2) repeats equation (1), with the correlation evaluated on S^{tr}, R^{tr} instead.

Under the optimization variable: “optimizing [say?] with an AI agent or prompt opt. or something.”

“Q: Is this how people ‘justify’ we can trust an LLM judge?
↳ at least literature — most important are frontier papers by Chinese companies!
→ Q: deep research.”

Transcription note: the page informally writes a distribution on the left of an argmax over judges. A type-consistent interpretation would first select a judge and then obtain its distribution. That correction belongs to interpretation and has not been silently substituted into the transcription.


## Page 2: loss-based judge selection

**TLDR:** Equation (3) evaluates a loss on validation data with help from training data; equation (4) directly optimizes the training-data loss. The prose asks to compare both.

Source: [original image](assets/handwritten_loss_selection.png). Original upload and SHA-256 are in manifest.json. Native source resolution is only 364 × 484 pixels. Brackets explicitly mark uncertain text; crossed-out text cannot be reconstructed reliably. Punctuation and equation layout are normalized.

“But I don't think (2) is [what happens / ideal?]. I conjecture:
1) (3) describes what [unclear] in real [world?] [crossed-out words; a small inserted note is illegible].
2) (3)/(4) is more ‘principled’/or at least it's easier to think about, since it uses the (successful) framework of ML learning (not necessarily ‘constrained’ learning theory).
3)” [No clearly legible text follows the third item.]

Equation (3):

\[
\widehat P_j^{AI_j}(\cdot)=\operatorname*{arg\,min}_{\widehat{AI}_j\in\Theta}
\{\operatorname{Loss}(\widehat P_j^{AI_j}(\cdot),P_j^H(\cdot))\}.
\]

Under argmin: “Constraint/helped by train data S^{tr}, R^{tr}.” Arrow from Loss: “on val set S^{val}, R^{val}.” [Some hats are uncertain.]

“Or what I think ppl do more in practice (in this, any [other?] [unclear] … [validation?] …)”

Equation (4) repeats equation (3), with Loss evaluated on S^{tr}, R^{tr}.

“→ (4) is more similar to what we do in practice. Do a [training?] thing on ‘all the data’. So coming to (3) feels especially important, but, in our setting with such small data, I wonder if trying to [unclear] … with val set … would give better [real results?].
Q: Do both experiments? Which one is the best?”

These are source questions. The precise definitions of train/validation data and the final independent test must be supplied by an experiment design, not guessed from the handwriting.


## Page 3: what does “best” mean?

**TLDR:** The note questions correlation as the only judge criterion, proposes comparing distributional losses, and asks for literature and intuition.

Source: [original image](assets/handwritten_distributional_objectives.png). Original upload and SHA-256 are in manifest.json. Native source resolution is only 364 × 484 pixels. Brackets mark uncertain text; these are not invented completions.

“Q: What does best mean in this setting?
→ the ppl/researchers report correlations with humans as the answer/result.
↳ but I conjecture correlations is not the right thing to be doing — it has disadvantages e.g. [Pearson only linear?], Kendall/Spearman → only [ordering?], etc. While some other [λ?] loss (Loss) that is KL div. [closeness?] [unclear] … integrates [unclear] more likely [unclear] the [target?] distribution of human judgments/preferences.
↳ So we can compare ‘all’ the metrics [it?] could be. See if (3), (4) with a [meaningful?] distributional [something] … CE with mean [unclear] (Wasserstein?), or [proper?] [unclear], or whatever … is best.”

Left list:

“→ corr: Pearson
Spear[man]
Kendall
Tau
others?”

Beside that list:

“+ show [papers?] relevant cuz I'm proposing to change the way we judge correlations/[validity?] for LLM judges.”

Bottom list:

“→ Loss:
– CE
– KL
– W
– TVD
– MMD [uncertain; another …D abbreviation is possible]
– others?”

Final line:

“→ intuition? — ppl [like/here?] have [accuracy?] …”

Interpretation, separate from transcription: CE commonly denotes cross-entropy; KL, Kullback–Leibler divergence; TVD, total variation distance. W may mean Wasserstein distance; MMD may mean maximum mean discrepancy. These are tentative readings; the chat context below documents the earlier weighted-distance proposal.


### Context recovered from the related chats — 11-07-2026

Brando's follow-up asked whether the unclear abbreviation referred to a weighted distance between probability distributions. In **Prepare human grading task**, his earlier request explicitly names **“weighted squared pmf loss”** (chat `01a1a8f9-dcb7-7381-9368-91d6e51faffd`, user turn `01a1b3a5-0664-7380-af84-babd23ded302`, 11-06-2026). The earlier handwritten note is transcribed in [experiment 06's mathematical note](https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/MATH_AND_NOTE.md):

\[
D_p(p,q)=\sum_{r=0}^{5}p(r)\bigl(p(r)-q(r)\bigr)^2.
\]

Here p is the human rating distribution and q is the judge's predicted rating distribution for the same input. For the six discrete rating categories, PMF means **probability mass function**; PDF means **probability density function** for a continuous outcome. This prior weighted-distance proposal is stronger contextual evidence than the tentative maximum mean discrepancy expansion, but it does not resolve the exact letters on this photograph.

The original [experiment 06 results](https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/RESULTS.md) include this weighted squared PMF distance as both a selection objective and a reported metric; its 25 selection folds completed. The later Wasserstein and Gaussian-kernel maximum mean discrepancy comparisons used separately stated definitions. Their results remain evidence about those definitions, not proof of what Brando's handwriting meant. No rerun follows from this terminology clarification.

## Page 4: related chat screenshot

**TLDR:** The screenshot shows the VeriBench project and four chat titles. Three are research chats; the first is a session-recovery chat.

Source: [original screenshot](assets/related_agent_chats.png). Original upload and SHA-256 are in manifest.json.

```text
veribench
  Find and revive Codex sessions
  Run Tiny-256 Lean prover comparison
  Prepare human grading task
  Check DT status in VeriBench
```

The first chat has a spinner-like indicator; the last three have blue dots. These indicators do not establish whether the underlying experiment is running or complete.
