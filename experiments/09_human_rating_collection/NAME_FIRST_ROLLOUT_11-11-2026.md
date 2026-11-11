# Name-first rating forms and project rules — 11-11-2026

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/NAME_FIRST_ROLLOUT_11-11-2026.md>

**TLDR:** Every active personal rating sheet now starts with the actual rater name, then the stable rater ID. Matching CSV snapshots and persistent Codex, Claude and Cursor rules make this the standard for every participant across the related projects.

## Forms and data

- [All 12 active Google Sheets and matching CSV table snapshots](sheet_exports/11-11-2026_all_raters_name_first/README.md): seven sheets updated in this pass, five already correct. Names and IDs were verified against the roster on every existing item row.
- [Snapshot manifest](sheet_exports/11-11-2026_all_raters_name_first/MANIFEST.json): source links, row counts, headers and file hashes. Each CSV's complete table equals its native readback. Leading instruction/comment rows and unused cells are omitted from the CSV table.
- Original table values, notes, validation and formatting were compared before/after the identity insertion: zero differences in retained cells. Browser checks confirmed readable name columns on all seven newly changed sheets at 100% zoom.
- [Slava's CSV-only warm-up](SLAVA_CSV_NAME_FIRST_11-11-2026.md): a separate current six-row form is prepared and unsent. The delivered archive remains unchanged.
- [Completion status](COMPLETION_STATUS.md): still 15 numeric warm-up ratings across Rylan, Sri and Yegor; no main ratings in the checked sheets. Naming and snapshots add zero observations and change no assignments.

## Persistent project rule

Every active personal Google Sheet and current CSV form/export starts with `rater_name,rater_id`. The name comes from the verified roster and is prefilled even on unanswered rows. The stable ID remains the join and deduplication key. A table snapshot matches its live sheet; separately enriched analysis exports label added coordinator metadata. Future revised warm-up and main forms use the same schema, differing in assigned items/rows. Preserve original imports and delivered archives; never fabricate responses or attestations.

The collection remains owned by this repository's experiment 09. Related projects link to [the identity/import workflow](IDENTITY_AND_IMPORT.md), rather than starting competing collections. Authorized named ratings are tracked; this rule does not expose credentials, private correspondence, consent records or sealed test data.

## Repository coverage and publication

Each project has this rule in `AGENTS.md`, `CLAUDE.md` and an always-applied Cursor `.mdc` file. Codex and Claude entries remain mirrored. The local paths below contain the rule; commit links record publication, not a claim that unrelated divergent local work has been synchronized.

| Project / local directory under `/Users/brandomiranda/` | Publication receipt |
| --- | --- |
| `trustworthy-theorem-judges` | Included with this receipt and the form changes on `main` |
| `cert-judge` | [0a47357](https://github.com/brando90/cert-judge/commit/0a47357221f4200c1461a4220a7db694ab1ac44d) |
| `judges-dont-need-psychometrics-or-corr` | [ba51ff1](https://github.com/brando90/judges-dont-need-psychometrics-or-corr/commit/ba51ff193f4bb880a79adc9f8d9c4782f4f98890) |
| `veribench` | [f267bdf](https://github.com/brando90/veribench/commit/f267bdf571365e99010975704ff3338246a53a17) |
| `vb-priv-bmg` | [ea9cc24](https://github.com/brando90/vb-priv-bmg/commit/ea9cc24644f636d7ca34f82edcc84c015585e7fc) |
| `veribench-blog` | [611d6d1](https://github.com/ehersch/veribench-blog/commit/611d6d177fbffd63fe8cb45d6ebd6474ac2a0253) |
| `veribench-dt`, also reached through the `veribench-inf` symlink | [f5b3ecf](https://github.com/brando90/veribench-inf/commit/f5b3ecf0bc651fe1fff4c91e9dd9020683003b06) |
| `veribench-deps` | [1f4c051](https://github.com/brando90/veribench-deps/commit/1f4c051a52f6c82be7686fb69d2ea2e1edc97e9c) |
| `vb-priv` | Local rule applied; remote `vals-ai/vb-priv` returned repository-not-found/404 through SSH Git, authenticated GitHub CLI and the GitHub connector. Remote publication is not claimed. |

The broad VeriBench family rule is conditional on handling human ratings; it does not turn a dependency or blog repository into a rating collector. Existing unrelated local work was preserved. Entry-file updates apply when clients load/read them; writing a rule does not prove an already-running session reloaded it.

## Verification

- 28 collection tests passed; project checks passed, including the prospective-design validator, mirrored instructions, source hashes and official paper style.
- Shared instruction-document checker passed with zero errors.
- Paper build passed with no overfull boxes or unresolved references. No paper source changed; the pre-existing PDF bytes were retained after build verification.
- CSV readback equality, source/export hashes, identity order and unchanged existing analysis exports were checked; `git diff --check` passed.

No collaborator email was sent. The team dispatch hold and Brando's warm-up-first workflow remain as recorded in the collection README.
