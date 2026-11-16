VERDICT: FAIL
CRITICAL_ISSUES: 0
MAJOR_ISSUES: 5
FIXES_APPLIED: 0
STRUCTURAL: SKIP
SUMMARY: Both archives pass file-integrity and sheet-mapping checks, but five major instruction/process issues need correction before delivery. No named-system leak was detected by the scans; residual provenance/style candidates and live download access remain unverified.

Reviewed 10-20-2026 by the Codex reviewer. This is a delivery review, not an assessment of any rating item.

Path aliases: `E = /Users/brandomiranda/veribench/experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml`; `B = E/human_round/private_ratings_setN/delivery/full_packet_staged_10-20-2026`; `P = E/human_round/sample_setN/packet`; `H = E/human_round`. References to `P` also locate the identical member within both ZIPs, after their top-level folder.

## Findings

A01 | MAJOR | P/START_HERE.md:7; P/START_HERE.md:8; P/human_judgements_prompt.md:44; B/qa/EMAIL_T01_DRAFT.txt:12; B/qa/EMAIL_T05_DRAFT.txt:12 | The emails direct both raters to their existing sheets, but the first packet step directs them to create a different sheet, and the rubric contains a third sheet destination. Following the packet-first instruction can split a rater's work across sheets or send the rater to the wrong round's template. | Give the delivery wrapper one authoritative sheet route: reuse the personalized email's sheet, create no new copy, and explicitly supersede both template-link instructions; preserve the scoring rubric and rebuild/version the wrapper and manifests together.
A02 | MAJOR | P/START_HERE.md:22; P/START_HERE.md:29; B/qa/EMAIL_T01_DRAFT.txt:16; B/qa/EMAIL_T01_DRAFT.txt:20; B/qa/EMAIL_T05_DRAFT.txt:16; B/qa/EMAIL_T05_DRAFT.txt:20 | The packet treats sharing as the final frozen submission and prohibits later edits, while the emails retain an earlier deadline for the original folders and invite continued extra work until 11-06-2026 in the same sheet. They do not explain how an already shared sheet signals a new submission or how earlier submitted ratings are preserved while extra folders are added. | Specify a concrete submission signal and coordinator-owned snapshot/version procedure for each deadline, state what remains editable, and explain how a rater marks their final submission.
A03 | MAJOR | P/START_HERE.md:9; P/START_HERE.md:27; P/START_HERE.md:29; B/qa/EMAIL_T01_DRAFT.txt:15; B/qa/EMAIL_T05_DRAFT.txt:15 | The packet asks for every included folder and completion before submission, whereas the emails make extra work optional; the packet's relative two-week deadline also conflicts with the retained original deadlines and the common extra-work deadline. A delivery on 10-21-2026 makes that relative deadline 11-04-2026, not 11-06-2026. | State that the full packet is available but only the original assignment is required, preserve each rater's original deadline, give extras the explicit 11-06-2026 deadline, and explain how incomplete or unrateable rows are left blank rather than guessed.
A04 | MAJOR | B/qa/EMAIL_T01_DRAFT.txt:25; B/qa/EMAIL_T05_DRAFT.txt:25 | The folding tip implies that Fold All isolates theorem statements by hiding proofs, but the command folds all foldable regions; indentation-based folding can hide parts of a multiline statement or an enclosing section. A reader with little Lean experience can therefore overlook material they are supposed to read. | Keep the Command Palette route, but advise selective proof-body folding and require expanding the complete statement, its hypotheses and any needed definitions; do not describe Fold All as a proof-only view. The official editor documentation supporting this finding is linked below.
A05 | MAJOR | B/qa/DELIVERY_PLAN.md:8; B/qa/DELIVERY_PLAN.md:10; B/qa/DELIVERY_PLAN.md:19; B/qa/DELIVERY_PLAN.md:22; H/PLAN_setN_rating_round.md:70; H/PLAN_setN_rating_round.md:101 | The proposed fixed full-packet order changes the recorded random whole-folder assignment procedure, but the send checklist does not require the coordinator's prospective protocol record or explain assignment for later qualifiers. Pair creation is conditional on both raters progressing, and a common numeric tail plus optional stopping can concentrate observations on the same early folders and confound task with practice/fatigue. | Add the coordinator's dated protocol/assignment disposition before sending: record the priority order, partial-folder and stopping treatment, actual two-rater coverage tracking, how additional raters fill deficits, and how primary versus extra ratings are handled without inspecting rating values; describe pairs as expected only after both complete the relevant folders.
A06 | MINOR | B/qa/EMAIL_T01_DRAFT.txt:25; B/qa/EMAIL_T05_DRAFT.txt:25; P/START_HERE.md:32; H/PLAN_setN_rating_round.md:37 | The packet prohibits artificial-intelligence assistance, but the recommended Cursor setup omits the plan's practical instruction to disable Cursor Tab; neither email repeats the independence rule. A novice may not distinguish passive editing features from AI suggestions. | Add a short instruction to disable AI completions and avoid AI chat/inline editing while rating, and to rate independently; retain the safe Command Palette shortcut.
A07 | MINOR | P/START_HERE.md:21; B/qa/EMAIL_T01_DRAFT.txt:22; B/qa/EMAIL_T05_DRAFT.txt:22 | The emails request elapsed folder time in the final row's problem_note, while the packet treats that field as optional and never explains the timing convention. | Put the same folder-time instruction in the delivery wrapper and explicitly distinguish this timing entry from optional explanatory notes.

## Checks run

- **Scope and instruction loading.** Read `BRIEF.md`, then `DELIVERY_PLAN.md` before the other review inputs; read both drafts, both structural comma-separated-value (CSV) snapshots, the supplied sent-log subset, both packet instruction documents, `make_rater_zip.py`, `PLAN_setN_rating_round.md`, and `RATER_INSTRUCTIONS.md`. Used numbered reads (`nl -ba` and Python `enumerate(..., 1)`) for the cited locations. No other private-ratings directory, sealed directory, judge output, experiment results file, or run directory was opened. No rating columns were accessed. A read-only helper supplied deterministic archive/CSV evidence; the Codex reviewer made the findings. Before the brief's no-Git constraint was loaded, the required home-configuration refresh ran `git -C /Users/brandomiranda/agents-config pull --ff-only`, returning `Already up to date`; no project Git command was run. The only authored file is this report.
- **Archive integrity.** In-memory Python `zipfile.ZipFile`, `testzip`, `hashlib.sha256`, `PurePosixPath` and `stat.S_ISLNK` checks passed for both archives: 178/178 unique safe members; 177/177 manifest-listed payloads match both their internal hashes and repository payloads; each internal manifest is byte-identical to the repository manifest; zero missing, extra, duplicate, unsafe, symlink or corrupt members. Every one of 25 folders has exactly five agent files a–e, one Python source and one reference file. There are zero dependency files in the source manifest or either archive. Both instruction files are present. Each archive is 741,276 bytes. Replacing only the 356 occurrences of the T01 top-level name in its raw ZIP bytes produces the T05 archive exactly.
- **ZIP metadata.** Compared timestamp, creator/extractor fields, flags, attributes, compression, comment and extra fields. All 125 agent entries have one identical metadata signature per archive, including timestamp 10-08-2026 00:00:00; archive/member comments and extra fields are empty. The only full-archive metadata split is compression: 177 payloads are deflated and the manifest is stored. This is not a system grouping signal.
- **Sheet structure.** Python `csv.DictReader` checks passed for 125/125 rows per snapshot: unique item IDs, correct rater IDs, valid task/item/path relationships, and exact one-to-one correspondence to the archive's 125 agent files. This checks only supplied columns A–D; it does not establish live-sheet permissions, rating-column validation or submitted values.
- **Instruction consistency.** Both packet/rubric and email use a 0–5 rating scale; the packet asks for the final score after the rubric's adjustment, and the emails do not introduce a different scale. The rubric's SHA-256 is `b29e9cafdab10463d29b6ffdbb4700b46ead0e6023278b9b7b69d9ef0ab350af`, matching the hash documented in `RATER_INSTRUCTIONS.md`. That separate older instruction page describes an earlier 75-item packet and is not shipped in either ZIP; do not substitute it for the set-N wrapper. The current delivered instructions contain the conflicts in A01–A03 and A07. Independence and no-AI rules are present in START_HERE.md.
- **Email IDs and dates.** Python JSON/string comparison found 2/2 matching sheet IDs and 2/2 matching original folder pairs against the supplied sent log: T01 (Rylan), N17/N21; T05 (Sri), N01/N23. `datetime.strptime(...).strftime('%a')` verified Tuesday 10-27-2026, Tuesday 11-03-2026 and Friday 11-06-2026. The original due dates are preserved correctly in the drafts; the deadline problem is the packet wrapper. Both drafts have four distinct blind-copy recipients and one expected Drive-link placeholder. Each draft is 306 whitespace-separated words including headers/signature; the length and appreciative tone are reasonable. The generic frontier-agent framing does not name a system, but neutral wording about the supplied agent files would avoid unnecessary capability expectations.
- **Editor tips.** Official documentation confirms Cmd+Shift+P for the Command Palette and Cmd+Backslash for splitting the editor; Cursor uses the Visual Studio Code defaults as its baseline. The drafts correctly avoid Cmd+K, which opens Cursor's inline AI editor. File > Open Folder and the optional multi-screen arrangement are reasonable; a split initially duplicates the current file, so opening the agent file in the second pane can be made explicit. Fold All's proof-only implication fails for the reason in A04. These were documentation checks, not a test of either rater's installation, keymap, operating system or Lean extension.
- **Order and pairing.** Parsed the numbered email lists, appended the remaining folders numerically, and checked 25 distinct folders per rater with zero omissions. Both orders follow all four stated plan stages. After both finish only their first two folders, there are 0 paired folders between these two raters; after both finish four, there are 4; after both finish twelve, there are 12; after both finish all 25, there are 25. If one finishes four and the other only two, there are 2 pairs. These are set-intersection calculations, not observed completion counts. The claim of eight currently unassigned folders was checked for agreement between plan and drafts only: the underlying assignment file is outside the permitted private-data scope and was not opened.
- **Scientific tradeoffs.** A predetermined order reduces deliberate folder choice, and keeping all five files together supports within-task comparisons when folders are completed. It does not remove volunteer selection, unequal stopping, missingness from partially completed folders, repeated-rater dependence, or shared practice/fatigue effects. More items rated by the same two people do not add independent raters. Full-packet exposure also permits cross-folder style recognition. Retain the full intended task/item denominator, distinguish planned from received pairs, and record this delivery change before collecting extras; no rating data were inspected or inferred to reach these design conclusions.
- **Delivery route.** The final rater emails contain links, not ZIP attachments, consistent with the supplied Stanford-mail constraint. The plan distinguishes Rylan's Stanford delivery address from the stated Google account for Drive sharing, and Sri's addresses agree. The intermediate ZIP email is directed to Brando's Gmail account; it is not itself the rater delivery. Uploads, recipient-account access, actual downloadability and placeholder substitution remain future send-time checks, not completed checks. There are 2/2 unresolved link placeholders by design. Before sending, the coordinator should bind each final link to the correct ZIP and named account, verify the downloaded bytes against the local SHA-256, and confirm that the Viewer permission permits downloading. No live Drive, Sheets or email action was performed; the supplied material alone does not independently prove account ownership or that a rater can download the file.

### Blinding scan and its limits

All 125 unique agent files were scanned; archive equality makes that scan applicable to both delivered copies. The read-only Python scans emitted counts, categories and locations only, never source text. They searched a common provider/model/harness-name vocabulary; explicit generation-attribution and provenance fields; runtime paths; dates, times and universally unique identifiers; external URLs; and recurring comment/header patterns.

- Named provider/model/harness-token hits: **0**. Explicit runtime paths, provenance ID fields, timestamp and identifier-pattern hits: **0**. Six generic attribution-phrase candidates had no nearby identity/runtime vocabulary; these are not established system leaks. Broad matches on ordinary words were not treated as provenance evidence.
- After whitespace normalization, **5 exact comment groups** recur across **3–5 task folders** each. They are potential style/boilerplate clues, not evidence that the files share an author or system. Representative locations, with no source text: `P/N01/agent_lean/N01d.lean:676` — recurring boilerplate; `P/N03/agent_lean/N03a.lean:41` — recurring boilerplate; `P/N03/agent_lean/N03a.lean:153` — recurring boilerplate; `P/N03/agent_lean/N03a.lean:287` — recurring boilerplate; `P/N12/agent_lean/N12d.lean:661` — recurring boilerplate.
- `P/N24/agent_lean/N24b.lean:8` — external repository-source link; provenance significance unresolved. Its destination was not visited. No system identity is inferred.
- A bounded opening-comment similarity check compared **110** eligible opening blocks (first 800 characters before a code fence, inline identifiers normalized), with **0** cross-folder edges at the reviewer-chosen 0.82 similarity threshold. This heuristic is not an anonymity guarantee. An initial unbounded comparison was interrupted and replaced by the bounded check; its incomplete run supplies no evidence.

A non-rater custodian should resolve the candidate markers before describing the packet as fully cleared of provenance clues. A confirmed nonsemantic identifier can be handled through a documented, versioned blinding change; never silently alter frozen or already rated evidence. No sealed identity mapping was consulted, and the scans do not establish or exclude authorship inference from style. The zero critical count means no critical defect was established here, not proof of perfect blinding or live delivery access.

### Reproducible integrity/order command

Run from the repository root. This is an in-memory, read-only replay of the deterministic integrity, CSV, date and pairing checks; it prints no rating content.

```bash
python3 - <<'CHECK'
from pathlib import Path, PurePosixPath
from collections import Counter
import csv, datetime, hashlib, json, re, stat, zipfile
E = Path('experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml')
B = E/'human_round/private_ratings_setN/delivery/full_packet_staged_10-20-2026'
P = E/'human_round/sample_setN/packet'
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest_bytes = (P/'FILES.sha256').read_bytes()
lines = manifest_bytes.decode().splitlines()
assert all(re.fullmatch(r'[a-f0-9]{64}  .+', l) for l in lines)
manifest = {l[66:]: l[:64] for l in lines}
assert len(manifest) == len(lines) == 177
assert all(sha((P/p).read_bytes()) == h for p,h in manifest.items())
assert {str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()} == set(manifest)|{'FILES.sha256'}
folders = {f'N{i:02d}' for i in range(1,26)}
agents = {f'{f}/agent_lean/{f}{a}.lean' for f in folders for a in 'abcde'}
fields = ('date_time','create_system','create_version','extract_version','reserved',
          'flag_bits','volume','internal_attr','external_attr','compress_type','extra','comment')
raw, orders = {}, {}
logs = {r['rater']:r for r in json.loads((B/'qa/sent_log_T01_T05_setN.json').read_text())}
for rid in ('T01','T05'):
    zpath = B/f'VeriBench_setN_{rid}_full_N01-N25.zip'
    raw[rid] = zpath.read_bytes()
    assert len(raw[rid]) == 741276
    root = f'VeriBench_setN_{rid}/'
    with zipfile.ZipFile(zpath) as z:
        infos = z.infolist()
        assert len(infos) == len({i.filename for i in infos}) == 178
        assert z.testzip() is None and not z.comment
        for i in infos:
            assert i.filename.startswith(root) and not i.is_dir()
            assert '..' not in PurePosixPath(i.filename).parts
            assert '\\' not in i.filename and not stat.S_ISLNK(i.external_attr >> 16)
            assert not i.extra and not i.comment
        payloads = {i.filename[len(root):]:z.read(i) for i in infos}
        assert payloads['FILES.sha256'] == manifest_bytes
        assert set(payloads) == set(manifest)|{'FILES.sha256'}
        assert all(sha(payloads[p]) == h and payloads[p] == (P/p).read_bytes()
                   for p,h in manifest.items())
        assert {'START_HERE.md','human_judgements_prompt.md'} <= set(payloads)
        assert {p for p in payloads if '/agent_lean/' in p} == agents
        assert {p.split('/')[0] for p in payloads if '/' in p} == folders
        for f in folders:
            for sub,n in [('agent_lean',5),('python_source',1),('gold_lean',1),('gold_lean_dependencies',0)]:
                assert sum(p.startswith(f'{f}/{sub}/') for p in payloads) == n
        signature = lambda i: tuple(getattr(i,k) for k in fields)
        assert sorted(Counter(signature(i) for i in infos).values()) == [1,177]
        assert list(Counter(signature(i) for i in infos if '/agent_lean/' in i.filename).values()) == [125]
    with (B/f'qa/sheet_structure_{rid}.csv').open(newline='') as f:
        rows = list(csv.DictReader(f))
    assert len(rows) == len({r['item_id'] for r in rows}) == 125
    assert [r['candidate_file'] for r in rows] == sorted(agents)
    for r in rows:
        assert set(r) == {'rater_id','item_id','task_folder','candidate_file'}
        assert r['rater_id'] == rid
        assert r['candidate_file'] == f"{r['task_folder']}/agent_lean/{r['item_id']}.lean"
    draft = (B/f'qa/EMAIL_{rid}_DRAFT.txt').read_text()
    assert logs[rid]['sheet_id'] in draft
    own = next(l for l in draft.splitlines() if l.startswith('1. '))
    assert re.findall(r'\bN\d\d\b',own) == logs[rid]['folders']
    order = []
    for l in draft.splitlines():
        if re.match(r'^[123]\. ',l): order += re.findall(r'\bN\d\d\b',l)
    order += sorted(folders-set(order))
    assert len(order) == len(set(order)) == 25
    orders[rid] = order
    for weekday,date in re.findall(r'\b(Tue|Fri) (\d\d-\d\d)\b',draft):
        assert datetime.datetime.strptime('2026-'+date,'%Y-%m-%d').strftime('%a') == weekday
    print(rid,'PASS',len(raw[rid]),sha(raw[rid]),'rows',len(rows))
assert raw['T01'].count(b'VeriBench_setN_T01/') == 356
assert raw['T01'].replace(b'VeriBench_setN_T01/',b'VeriBench_setN_T05/') == raw['T05']
print('paired folders at equal progress:',[(k,len(set(orders['T01'][:k]) & set(orders['T05'][:k]))) for k in (2,4,12,25)])
CHECK
```

The content scan used Python regular-expression iteration over `P.glob('N*/agent_lean/*.lean')`, location-only output, whitespace-normalized comment hashing with `sha256`, and `difflib.SequenceMatcher` on bounded opening comments. The repeat filter required at least 55 characters and seven alphabetic words of length three or more, occurring across at least three folders. These are reviewer-chosen search heuristics, not validated blinding tests. A separate line-level repeat search (at least 60 characters and ten alphabetic words, across four folders) found zero groups. No model-based rating, Lean compilation or proof assessment was performed or needed for this delivery review.

### Evidence hashes

| Artifact | SHA-256 |
|---|---|
| T01 archive | `77f3f13c4237883827ae20e6f01c230d39f0e171d47b5d1fc85842e66b62cb65` |
| T05 archive | `9a04f963d25f025c9a50ba51a5ba93006741ced63e40e6a7e5c9021ecb2fb92d` |
| Repository and both internal manifests | `fecfe1e4511f9a8e7e6045dfc5e81d98d7bb48736f54d7e4df75bac2c18785b3` |
| Delivery plan | `ad56ff93cf96029572008f28b121d7256b3d08d0f3652059a0783f45ad53a7cf` |
| T01 draft | `bb259a7c2ab3da6c3f44a74e9805694dd167a1215c1e3b808ec4c6416767068d` |
| T05 draft | `ac0de3225e49d6fbfb6cb3b1de6cef0a6589f3f2f1ffe3f55e13a35f4033b843` |

All 11 pinned review-input hashes (the six entries above plus the sent log, two structural sheets and two instruction documents) were rechecked immediately before writing this report.

### Editor sources checked on 10-20-2026

- [Visual Studio Code default keyboard shortcuts](https://code.visualstudio.com/docs/reference/default-keybindings): Command Palette and split editor.
- [Visual Studio Code folding documentation](https://code.visualstudio.com/docs/editing/codebasics#_folding): Fold All targets all regions; default folding is indentation-based. The warning about hidden statement material is an inference from that documented behavior, not an observed rating error.
- [Cursor keyboard-shortcut reference](https://cursor.com/docs/reference/keyboard-shortcuts): Command Palette and Cmd+K inline editing.
- [Cursor shortcut baseline](https://cursor.com/help/customization/keyboard-shortcuts): Visual Studio Code defaults plus Cursor AI shortcuts.
- [Cursor Tab completion](https://cursor.com/help/ai-features/tab): AI suggestions and the controls for disabling them.
