# Handwritten notes: correlation formulations 1 and 2

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/support/assets/notes_correlation_formulations_1_2_11-09-2026.md>

**TLDR:** Formulation 1 selects a developed judge by validation correlation; formulation 2 optimizes a judge using training correlation. The note asks whether the literature actually uses these procedures; it does not establish that claim.

Source: Brando Miranda's [original photograph](notes_correlation_formulations_1_2_11-09-2026.jpeg), supplied on 11-09-2026. Original path: `/Users/brandomiranda/Downloads/WhatsApp Image 2026-11-09 at 10.44.48.jpeg`. See [image provenance](formulations_11-09-2026_provenance.json).

## Transcription

“I figured out what the correlation formulation is doing…”

**(1)**

\[
P_j^{\widehat{AI}_j}(\cdot)
=\operatorname*{argmax}_{\widehat{AI}_j\in\Theta}
\operatorname{Corr}\left(\widehat P_j^{AI_j}(\cdot),P_j^H(\cdot)\right).
\]

Annotations: the candidate judges are “constrained/helped by” \(S^{\mathrm{tr}},R^{\mathrm{tr}}\); correlation is evaluated using \(S^{\mathrm{val}},R^{\mathrm{val}}\).

“→ This is what people are doing.

↳ TODO: deep research to justify/cite if this is true.

I actually think this is more true!”

**(2)**

\[
P_j^{\widehat{AI}_j}(\cdot)
=\operatorname*{argmax}_{\widehat{AI}_j\in\Theta}
\operatorname{Corr}\left(\widehat P_j^{AI_j}(\cdot),P_j^H(\cdot)\right).
\]

Here the correlation is annotated with \(S^{\mathrm{tr}},R^{\mathrm{tr}}\).

Below the optimization variable: “optimizing, e.g. with an AI agent or prompt opt. or something.”

“Q: Is this how people ‘justify’ we can trust an LLM judge?

↳ at least literature — most important are frontier papers by Chinese companies!

→ Q: deep research.”

## Reading notes

The handwritten hats vary slightly between expressions; the typesetting retains the intended distinction between the selected judge and its predictions. “Constrained/helped” is a close reading of the small annotation, not a formal constraint. The final company phrase appears to read “Chinese companies”; it is not a statement about the literature's actual coverage. The attached TODO requests are transcribed as source content, not treated as instructions to launch an exhaustive separate project.
