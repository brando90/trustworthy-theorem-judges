<!-- TLDR: Resume checkpoint for experiment 110's VBV2 condition (FSC judge transfer to VeriBench V2) and, from the same session, the agent-spec v8 namespace fix; both are DONE and on main, and nothing from this session is running. -->
# CKPT: experiment 110 VBV2 condition + agent-spec v8 namespace fix (session 69e8c572)

Created: 10-13-2026 11:06 PDT
Last updated: 10-13-2026 11:06 PDT

- **Status: DONE.** Both of this session's tasks are on `main`. No step is pending, so the next agent has nothing to resume.
- **Task 1 (last active): experiment 110 VBV2 condition.** Brando's weekly-notes task of 10-09-2026: do VeriBench V2 (VBV2) frontier-model outputs resemble the 75 human-rated items the H2 FSC (formal specification coverage) judge was validated on?
  - **Landed:**
    - pre-registration `f1bfbe3564` ([CRITERIA_VBV2.md](CRITERIA_VBV2.md)), committed before any VBV2 value was computed;
    - results `e2c8d7de03`: [RESULTS_judge_transfer_vbv2.md](RESULTS_judge_transfer_vbv2.md), [results.md](results.md) and [results/results_vbv2.json](results/results_vbv2.json).
  - **Result:** pooled VBV2 frontier models are in distribution on 11/15 criteria [8–11], "partially in-distribution"; the pre-declared prediction (k ≤ 7) is refuted.
  - **Verified:**
    - experiment 110's frozen `analyze.py` (`d33b23b5…`) and `extract_criteria.py` (`d72481b8…`) were used unmodified;
    - 3/3 seeded pool rows reproduce;
    - the committed scripts match the hashes recorded in the results JSON (`gather_vbv2_on_snap.py` `978f4501…`, `analyze_vbv2.py` `c13edd57…`).
  - **Amendment V-A1** (experiment 100's phase-7 cells as a separate secondary source): decided in the gather script before the analysis ran; appended to CRITERIA_VBV2.md in the results commit.
  - **Private files:** per-item rows and texts are on SNAP at `/dfs/scratch0/brando9/vb110_vbv2/` (mode 700). No FSC level is written anywhere, because Brando is rater A1 in experiment 102's round.
- **Task 2 (earlier): agent-spec v8 namespace fix and damage audit.**
  - **Landed:**
    - v8 in `e7452de7a0` (PR #502);
    - audit report `bb19a9b318` + `99e58c20d4` in `experiments/ideas/rl4cv_factored_scsc_results_implications_for_vb/namespace_defect_v8/`;
    - paper §3 "version 8" `1efbef1c64`; experiment 103's v6 label `9a972711c7`; experiments-index row for 107 `6a77bdeb2c`.
  - **Closed on 10-12-2026** by experiment 109's worker (`ef598fbbdc`; files in 109's `results/namespace_reaudit/`).
    - Mistral Medium 3.5: 3 of 57 defective files compile once the name is quoted. That is at or below the pre-declared 18, so there is no v8 Mistral-only condition.
    - The other 7 public systems: 0 of 6,264 files defective.
  - **Private audit files:** SNAP `/dfs/scratch0/brando9/vb_ns_audit_10-09-2026/` (mode 700).
- **Live jobs: none expected.**
  - Last verified on 10-09-2026:
    - mercury1 had no audit session or process at ~14:22 PDT; later runs there were foreground commands that finished.
    - skampere3 had none at ~15:00 PDT, after its owner stopped the watcher (pid 941936).
  - The re-check at 10-13-2026 11:05 PDT failed: ssh to skampere1, skampere3 and mercury1 timed out. The current SNAP state is therefore unverified.
- **Blockers:** none.
- **Unanswered message:** on 10-09 this session told experiment 107's owner session that five `private/bin` processes were still running on skampere2 after `T2V3_DONE`. That session was offline and any reply is unverified. They are not this session's processes.
- **Optional follow-ups (not started, not owned here):**
  - human ratings of a small VBV2 sample, the only way to validate the judge on VBV2 (belongs to experiment 102's rating round);
  - re-running this condition on VBV2.1 outputs once experiment 99 has them.
- **Exact commands to re-run the VBV2 condition.** For VBV2.1, first adapt `gather_vbv2_on_snap.py` to experiment 99's judge-prompt format (unverified) and record that as a dated amendment.
  ```bash
  E=experiments/110_fsc_judge_transfer_frontier_outputs_vs_human_rated_pool; D=/dfs/scratch0/brando9/vb110_vbv2; S=<private scratch dir>
  scp $E/vbv2_condition/scripts/gather_vbv2_on_snap.py $E/scripts/extract_criteria.py brando9@skampere1.stanford.edu:$D/code/
  ssh brando9@skampere1.stanford.edu "cd $D/code && python3 -I gather_vbv2_on_snap.py $D/out $D/code"
  scp brando9@skampere1.stanford.edu:$D/out/vbv2_features.jsonl $S/
  python3 $E/vbv2_condition/scripts/analyze_vbv2.py $S/vbv2_features.jsonl $S/out
  ```
