# SIMULATED rating dry run: persona of rater T02 (name withheld)

**All simulated. Not real ratings, not real data. Never mix with real ratings. Nothing was sent to rater T02 or any real rater.**

- Who did it: GPT-6 Astra, xhigh reasoning, run through Codex (CLI) as a frontier model, per Brando's "should be with frontier models". The persona was written by Claude Code (Sonnet 5.5) from public information only: a research scientist in software-engineering productivity and AI measurement with an expert-panel rating style; no Lean-specific work found.
- Inputs it got, nothing else: the rater email (final Thursday 11-19, 6pm PT wording) and rater T02's packet (rating_packet_native-heavy-11-11-2026_T02.zip: 4 files in task_11_html_escaping and task_14_statistical_quantiles).
- Route: the packet's ratings.csv route (the Google Sheet is not reachable for a simulation). Two parallel runs, one per task folder; merged here. Only the rater's name and the persona's source list were replaced by the code T02 (the privacy rule in this folder); scores and text are otherwise as produced.
- Not checked: whether a real Lean build passes; I spot-checked only that agent_1/agent_3 of task 14 contain no shift theorem (grep: 0 matches, the reference has 26) and that foldl_append_init exists in task 11's reference.
- Scores: task_11 agent_2 = 4, agent_3 = 4; task_14 agent_1 = 3, agent_3 = 3.

---

## Task 11 (html escaping)

All content, including the CSV ratings, attestations and time estimates, is simulated and is not real participant data.

Scope: only the two files in task_11_html_escaping, as specified by PART. The statistical-quantile files are excluded.

The simulated persona uses localized AI help to interpret `flatMap`, folds and `Id.run`, then independently compares statements and selects scores; `yes` represents that hypothetical workflow. Times are estimates, with shared instruction and folder-reading time included once in agent_2.

1. agent_2.lean — A: Yes; B: Yes; C: No; D: N/A. Base: 4; spam adjustment: 0; final: 4.

   `characterwise_thm` supplies the gold replacement behavior; `append_thm` and the singleton encoding recover `ordering_thm`, and these jointly recover the gold correctness postcondition.
   `functional_imperative_thm` supplies implementation equivalence; `.str s` preserves the full gold input domain. The arbitrary-function, arbitrary-accumulator statement `foldl_append_init` is missing: the escape-specific append law does not cover its generality.

2. agent_3.lean — A: Yes; B: Yes; C: No; D: N/A. Base: 4; spam adjustment: 0; final: 4.

   `escape_single_pass_thm` matches the gold characterwise fold, while `escape_append_thm` and the singleton encoding recover ordering and hence the gold correctness postcondition.
   `escapeImp_eq_escape` and `escapeLoop_eq_escape` cover implementation equivalence without restricting gold inputs. The accumulator lemmas concern particular encoders, leaving the general `foldl_append_init` statement uncovered.

For both files, supporting lemmas, additional relevant properties and executable examples are not obvious theorem spam. Proof bodies and test outcomes were not used to judge coverage. The 4-versus-5 uncertainty concerns whether the generic gold helper is itself a target; I included it and applied the lower-score tie-break. Excluding that helper would make both scores 5.

What was confusing or unclear:

- **Gold target scope:** The rubric does not distinguish specification guarantees from supporting theorem statements such as `foldl_append_init`. Fix: explicitly list scored gold declarations and excluded helpers.
- **CSV versus Sheet:** The email assigns the Sheet, while START_HERE permits CSV only when explicitly assigned. This simulation supplies that assignment, but the actual unreachable-Sheet fallback lacks return instructions. Fix: specify when CSV is permitted and where to submit it.
- **Attestation:** One answer combines AI use and independent judgment; an independent rater who used no AI must answer `no`. Fix: separate AI-use reporting from the independence attestation.
- **Spam and large files:** “Handful,” “dominates” and “up to” leave classification and deductions unspecified, especially for extensive tests and supporting lemmas. Fix: provide examples and deduction criteria; clarify that length alone is insufficient.
- **Time accounting:** Shared folder time is addressed, but general instruction-reading and localized AI-help time are not explicit. Fix: define included activities and charge general setup once.
- **Checklist B:** “Preconditions preserved or strengthened” can suggest that restricting the input domain improves coverage. Fix: require coverage of every gold-admissible input while allowing stronger conclusions.

What the simulated persona would likely ask Brando by email:

“Should proof-support statements such as `foldl_append_init` count as coverage targets? I assigned both HTML files 4 conservatively; both cover the main escaping guarantees. Also, if the Sheet is unavailable, where should I return the CSV, and should extensive relevant helper lemmas and tests be excluded from theorem spam?”

---

## Task 14 (statistical quantiles)

All content, including the CSV ratings, attestations and time estimates, is simulated and is not real data from simulated rater T02.

Scope: Only the two task_14_statistical_quantiles files are assessed, as required by PART. The task_11 files are outside scope.

The simulated persona uses localized AI assistance for Lean notation such as Pairwise, Option/Except and n.toNat, then independently compares statements and selects scores; this explains the simulated “yes” attestations. The first file’s 45 minutes includes approximately 20 minutes of shared instructions, Python and reference reading; the second file has 35 minutes allocated.

I treated length, permutation invariance, shift invariance and functional-imperative equivalence as independent principal targets. Gold correctness bundles the first three. A=Y requires complete key-target coverage; B=Y requires preservation of the full gold contract. Definitions were inspected to interpret statements; proof quality and execution were not assessed.

- agent_1.lean — A=N; B=N; C=N; D=not applicable; base=3; spam adjustment=0; final=3.
  succeeds_thm plus length_thm recover successful output of length n−1, and perm_invariant_thm covers permutation invariance on rational inputs.
  No shift-invariance statement or imperative equivalence is present, so correctness does not recover the full gold postcondition; the raw-Rat domain and typed error guarantees also lack counterparts.
  Helpers and examples concern quantiles and are not obvious spam; two principal guarantees are covered, supporting partial coverage rather than the rubric’s “less than half” category.

- agent_3.lean — A=N; B=N; C=N; D=not applicable; base=3; spam adjustment=0; final=3.
  length_thm and permutation_thm cover the corresponding guarantees, while benchmark_equivalence_thm supplies unconditional functional-imperative equivalence for arbitrary NumericOps.
  No statement relates arbitrary shifted inputs to shifted outputs, and correctness_thm omits this central gold conjunct, including the gold’s special zero-denominator shift case.
  Bounds, monotonicity, median, constant-sample and test statements are relevant additions, with no obvious spam; the missing central guarantee is an important gap, so 4 is not justified.

What was confusing or unclear:

- Submission route: The email and START_HERE assign the Sheet, while CSV requires explicit assignment; this simulation supplies that override. Suggested fix: specify an inaccessible-Sheet fallback and exactly where to return the CSV.
- Coverage counting: The reference includes many Bridge helpers, examples and an aggregate correctness theorem, but the rubric does not define the denominator for “less than half.” Suggested fix: enumerate independently scored guarantees and explain how helpers and bundled contracts count.
- Recoverable guarantees: “A small set of lemmas” has no worked boundary. I did not credit shift invariance merely from an exact interpolation formula without a clear short recovery involving shifted sorting and arithmetic. Suggested fix: provide examples of acceptable indirect coverage.
- Representation changes: Gold Rat permits noncanonical fractions and zero denominators; ℚ excludes the latter, and Option discards error details. The gold explicitly handles these cases, so I did not assume a reference defect. Suggested fix: specify acceptable representation mappings and whether malformed values and exact errors are required.
- Spam and long files: “Handful,” “dominates” and “up to” leave penalty selection open; relevant helpers and tests create substantial length. Agent_1 also advertises absent sections. Suggested fix: give penalty examples, provide a declaration index and check introductory claims against supplied contents.
- Attestation and timing: The compound attestation makes “no” ambiguous between no AI use and failure to retain independent judgment; allocation of general onboarding time is unspecified. Suggested fix: separate AI-use and independence questions and assign shared onboarding to the first rated file.

What the persona would likely ask Brando by email:

“Can I return the CSV when the Sheet is inaccessible, and where should I send it? Should I accept ℚ/Option as abstractions of the reference’s raw Rat/Except, or require coverage of zero-denominator values and exact errors? Please also confirm the independently scored targets and how much derivation qualifies an unstated guarantee as covered.”
