<!-- TLDR: Recruitment email for rating set N (C10–C12): Brando asks the VeriBench team (all authors plus Amy Lu and Ethan Lee; Sanmi Koyejo and Bo Han in bcc; Brando included as a rater) to commit time to blinded coverage ratings of frontier-agent Lean files; final text for the 10-05-2026 send after a light QA. -->
**SENT 10-05-2026 19:20 PDT (2026-10-06T02:20:37Z), Gmail message `1a10f0351cdda5f8`, from brandojazz@gmail.com.** The headers were verified: To = the 27 addresses below (Brando included); Bcc = Sanmi Koyejo and Bo Han. The thread showed no bounce. Light QA (Codex `gpt-6-astra`, ultra, session `01a10ef9`): round 1 FAIL with 1 critical (C8.5 neutral briefing); the driver fixed it; Brando-requested confirmation round: PASS, 0 critical, 0 major, 4 fixes applied. Replies are due Fri 10-09-2026.

**Addition 10-07-2026:** Simon Obstbaum (an author) was missing from the 09-29 team list this email reused. The list had not been cross-checked against the paper's 28 authors; the other 27 were covered. He was sent the same text, with a one-line apology and Yegor's pointer, at simon@obstbaum.eu (address from Yegor Denisov-Blanch via Brando), cc brando9@stanford.edu, Gmail message `1a117959882fa859`. Yegor says Simon needs about one week of lead time.

**Reminder 10-08-2026: SENT 09:41 PDT (2026-10-08T16:41:10Z), Gmail message `1a11c63e1ca626ed`, on the same thread.**
- **From and to:** brandojazz@gmail.com to the 27 recipients below plus simon@obstbaum.eu. CC brando.science@gmail.com and brando@vals.ai; Bcc Sanmi Koyejo and Bo Han. Headers verified.
- **Content:** the plan's draft A, shortened. No Lean expertise is needed (raters compare statements; no proofs). Each file needs two ratings (C15). There is a 30–45 minute warm-up, then 2–3 folders. Please reply yes or no by Fri 10-09. Neutral per C8 item 5.

**Vendor request 10-08-2026: SENT 2026-10-08T16:41:14Z, Gmail message `1a11c63f12adbf9e`.**
- **From and to:** brandojazz@gmail.com to nikil@vals.ai (address verified against his earlier emails). CC brando.science@gmail.com and brando@vals.ai.
- **Ask:** that Vals recruit Lean-fluent graders through the Lean Zulip, as for ProofBench, for about 35 folders (about 40–70 hours over two weeks).
- **Questions:** whether contractors may see the internal model's files (C15 item 2), contracts or payment, and whether packets go through Nikil or directly to graders.

**FINAL TEXT (10-05-2026), sent only after the light QA verdict.** The light QA (Codex `gpt-6-astra`, ultra, session `01a10ef9`) returned FAIL with 1 critical issue: the motivation cued the expected outcome, against C8 item 5's neutral briefing. Its suggested neutral wording, the workload and timeline fixes, and the explicit recipient list below were applied.

**Recipients (verify the headers against this list before sending).**
- **To (27):** brando9@stanford.edu, vatsava@gmail.com, ehersch@stanford.edu, cszkzhou@comp.hkbu.edu.hk, aimingnie@gmail.com,
  daneshva@stanford.edu, aniva@stanford.edu, iddah@stanford.edu, kacharya@stanford.edu, eobbad@gmail.com, soylu@stanford.edu,
  wkirk@stanford.edu, zixiaowang@g.harvard.edu, kaif@stanford.edu, louisely@stanford.edu, poin@stanford.edu, rakshitk@stanford.edu,
  srliu@stanford.edu, ydebl@stanford.edu, stevendi@stanford.edu, santiago@galois.com, sarracino2@llnl.gov, rschaef@cs.stanford.edu,
  mohittiwarinyc@gmail.com, lukedhlee@berkeley.edu, amylucky@stanford.edu, eth127@stanford.edu.
- **Bcc (2):** sanmi@cs.stanford.edu, bhanml@comp.hkbu.edu.hk.
- Brando's own ratings are A1 sensitivity ratings (C8.3/C10). Folder assignment must still give every file three primary, non-A1 ratings.
- **Send.** From brandojazz@gmail.com, the account of the 09-29-2026 team email, "VeriBench naming change".
- **To:** the 09-29 team list with Brando (brando9@stanford.edu) included. Two addresses that bounced on 09-29 are replaced from Brando's own contacts: srivatsavad@stanford.edu → vatsava@gmail.com, eobbad@stanford.edu → eobbad@gmail.com.
- **Bcc:** Sanmi Koyejo, Bo Han.
- **Content checks.** No pilot timing exists (Brando skipped the pilot on 10-05-2026), so the hours are an estimate from file sizes and are labelled that way. No internal model is named.

---

**Subject:** VeriBench: can you help rate AI agents' Lean files? (please reply by Fri 10-09)

Hi all,

I'm putting together a small human rating panel for VeriBench and would love your help. I'm rating too.

We're checking how well our automatic judge agrees with human ratings on current coding agents' Lean files. Your ratings will also measure directly how well those files' theorem statements cover the reference specifications.

- **What you'd do.** Each task folder has a short Python program, its reference Lean file and several agent Lean files, blinded and in random order. You give each agent file one 0–5 coverage score in a CSV sheet, using the same rating instructions as our May round. You don't need to check proofs, only whether the agent stated the right properties.
- **How much.** Every file needs three independent ratings, so we'll split whole task folders across raters. Budget roughly 1–2 hours per folder, possibly longer: this is an unmeasured estimate from file sizes, and today's agents write long files. With about twelve raters, that's 6–7 folders each, roughly 6–14 hours overall, spread over as many sessions as you like.
- **Ground rules.** Please rate on your own, without AI tools, and don't discuss items until everyone has returned their sheet.
- **Timeline.** The packet isn't ready yet; some agent runs are still pending. I'll send your folders when it's ready, with sheets due two weeks after delivery.

Could you reply by Friday 10-09-2026 with yes or no, and roughly how many hours you could give? Even a couple of folders helps.

Thanks so much!
Brando (drafted with Claude)
