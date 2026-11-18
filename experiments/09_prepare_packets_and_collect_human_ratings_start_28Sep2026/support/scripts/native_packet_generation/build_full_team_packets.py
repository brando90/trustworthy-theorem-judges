"""Plan, build and verify the full-team rating packets (one per rater).

Current round (11-16-2026): 100 files = 25 tasks x 4 agents (GPT-6 Astra, Claude
Fable 5.1, Grok 4.7 and Gemini 4 Argon); see build_four_agent_cohort.py.
The 75-file round (11-14-2026) used RATABLE_COHORT_75_V2.json and sealed/builds.

    plan    write the private roster/design and one Sheet request file per rater
    build   build every rater's packet and unsent email text
    sheets  add the new rows to each live Sheet in place (existing rows and any
            entries move with their rows), then bind the build to the live table
    verify  bind each build to a digest read in the owner's browser (fallback)
    drafts  replace each rater's unsent email draft with the current one (nothing is sent)
    send    THE one send path: dry run by default; `send --confirm --all` (or rater IDs) sends each
            saved Gmail draft as it stands, skips anyone already sent, then trashes that draft
    export  write each live Sheet's exact table to ratings/ and refresh RAW_MANIFEST/SUMMARY
    review  write REVIEW_ALL_31_EMAILS_<date>.md from the current drafts (after `drafts`)
    status  who is grading: live per-rater progress, written into the experiment README

Row order (100-file round): Brando (A1) works in task order. Every other rater keeps
the exact random order of their live 75-file Sheet (11-14-2026 build receipts) and
the 25 new rows are inserted one at a time at hash-seeded uniform positions, so each
order stays a uniformly random permutation. Order never uses file content or scores.
(The task-grouped design() below was the 11-14 plan; the live Sheets used a per-rater
hash order instead, which this round preserves.)
"""

from __future__ import annotations

import csv
import hashlib
import io
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from source_label import add_label as add_source_label  # noqa: E402
import build_packet as bp  # noqa: E402

REPO = HERE.parents[4]
EXPERIMENT_DIR = HERE.parents[2]
OUT = REPO / "research_artifacts/09_human_rating_collection/preparation_11-09-2026/full_team_11-14-2026"
SEALED = OUT / "sealed"
# Rounds: "100" = first 100-file packet (11-16-2026, Grok and Gemini files from Terminus 2);
# "100_native" = same rows and file names, every file from its vendor's own harness (build_native_cohort.py).
ROUND_TAG = "100_native"
COHORT = SEALED / {"100": "RATABLE_COHORT_100_FOUR_AGENTS.json", "100_native": "RATABLE_COHORT_100_NATIVE.json"}[ROUND_TAG]
BUILDS = SEALED / f"builds_{ROUND_TAG}"
BUILD_INDEX = SEALED / f"BUILD_INDEX_{ROUND_TAG.upper()}.json"
DRAFTS_DIR = SEALED / f"drafts_{ROUND_TAG}"
DRAFTS_LOG = SEALED / f"DRAFTS_SAVED_{ROUND_TAG.upper()}.json"
SHEET_REGISTRY = OUT / "SHEET_REGISTRY.json"
SHEETS_API = "https://sheets.googleapis.com/v4/spreadsheets/"
TAB = "Ratings"
TEMPLATE_SHEET_ID = "1Hpcb4NP754RDWstDkiaTR59K9AX2vXNL6IR9iXKRo-Y"
TEMPLATE_TAB_ID = 0
BRANDO_SHEET_ID = "1zUDr9fpUwK0IuxrSdFfBR_mOt4WwMY8-doBC6cIhIHM"
# Brando, 11-17-2026: "I changed the deadline for Monday 6pm" / "isn't the subject too long? Can it be shorter?"
DEADLINE = "Monday, 11-23-2026"
SUBJECT = "VeriBench rating task: due Mon 11-23, 6pm PT"
# Every subject this email has used, so drafts and sends are matched across the rename (T05/V02 went out under the first).
SUBJECTS = ("VeriBench human-rating main rating task", "VeriBench rating task: due")
# Brando, 11-13-2026 (agents-config personal/email-signature.md): BCC only brando.science unless he asks.
# Brando, 11-17-2026: rater emails are his own draft text only (see brando_draft): "STOP PUTTING GARBAGE LIKE THIS".
BCC = ["brando.science@gmail.com"]
# Brando, 11-17-2026: "cuz stanford removes the zip file attached. Instead create a zip copy to my gdrive and send that
# linke". Stanford's mail filter removed the attached .zip from Yegor's copies, so the email links one shared copy of the
# packet zip on his Drive (anyone with the link can view) and attaches nothing. Every unsent rater's zip is byte-identical.
PACKET_DRIVE_URL = "https://drive.google.com/file/d/1OcX6JT9faUIo0bSp0I9wnQMPctIjedRT/view?usp=sharing"
PACKET_ZIP_SHA256 = "ab78870c0577c6de9243a3f5ef0155b4ab73c52eff889c45f542b0ca8360a387"  # the file at PACKET_DRIVE_URL
COAUTHOR = ("Would you be willing to help with a human-rating task for VeriBench? Your ratings would be really "
            "valuable, and if you are interested and have time, I would be happy to add you as a co-author on "
            "the papers this data is used for. No pressure at all.")
OPENERS = {
    "coauthor": COAUTHOR,
    "varun": COAUTHOR + " Doing these ratings is also a great way to get intimately familiar with Lean 4 "
             "autoformalization\u2014and if you have seen Andrej Karpathy's and Rylan Schaeffer's advice on "
             "becoming a top machine learning researcher (for example, how much of ImageNet Karpathy inspected "
             "firsthand), looking closely at the actual data yourself is essential.",
    "weekend": "Your ratings would be extremely valuable. If you can finish early, that would be even "
               "better, as many ratings as you have time for.",
}
# rater_id, verified name, greeting, delivery email, group, opener (aligned with RATER_IDENTITIES.json & ROSTER.csv)
PEOPLE = [
    ("T01", "Rylan Schaeffer", "Rylan", "rschaef@cs.stanford.edu", "author", ""),
    ("T02", "Yegor Denisov-Blanch", "Yegor", "ydebl@stanford.edu", "author (extra-only designation preserved)", ""),
    ("T03", "Dilara Soylu", "Dilara", "soylu@stanford.edu", "author", ""),
    ("T04", "Allen Nie", "Allen", "aimingnie@gmail.com", "author", ""),
    ("T05", "Srivatsava Daruru (Sri)", "Sri", "vatsava@gmail.com", "author", ""),
    ("T06", "Donald Poindexter Jr", "Don", "ddpoindexterjr@gmail.com", "author", ""),
    ("T07", "Simon Obstbaum", "Simon", "simon@obstbaum.eu", "author", ""),
    ("T08", "Amy Lu", "Amy", "amylucky@stanford.edu", "new co-author invite", "coauthor"),
    ("T09", "Ethan R Lee", "Ethan", "eth127@stanford.edu", "new co-author invite", "coauthor"),
    ("T10", "Ethan Hersch", "Ethan", "ehersch@stanford.edu", "author", ""),
    ("T11", "Kirill Acharya", "Kirill", "kacharya@stanford.edu", "author", ""),
    ("T12", "Rakshit Kaushik", "Rakshit", "rakshitk@stanford.edu", "author", "weekend"),
    ("T13", "Zhanke Zhou", "Zhanke", "cszkzhou@comp.hkbu.edu.hk", "author", ""),
    ("T14", "Daneshvar Amrollahi", "Daneshvar", "daneshva@stanford.edu", "author", ""),
    ("T15", "Leni Aniva", "Leni", "aniva@stanford.edu", "author", ""),
    ("T16", "Iddah Mlauzi", "Iddah", "iddah@stanford.edu", "author", ""),
    ("T17", "Elyas Obbad", "Elyas", "eobbad@gmail.com", "author", ""),
    ("T18", "Weston Kirk", "Weston", "wkirk@stanford.edu", "author", ""),
    ("T19", "Zixiao Jolene Wang", "Zixiao", "zixiaowang@g.harvard.edu", "author", ""),
    ("T20", "Kai Fronsdal", "Kai", "kaif@stanford.edu", "author", ""),
    ("T21", "Ying Li", "Ying", "louisely@stanford.edu", "author", ""),
    ("T22", "Shurui Liu", "Shurui", "srliu@stanford.edu", "author", ""),
    ("T23", "Steven Dillmann", "Steven", "stevendi@stanford.edu", "author", ""),
    ("T24", "Santiago Cuellar", "Santiago", "santiago@galois.com", "author", ""),
    ("T25", "John Sarracino", "John", "sarracino2@llnl.gov", "author", ""),
    ("T26", "Donghyun Lee", "Donghyun", "lukedhlee@berkeley.edu", "author", ""),
    ("T27", "Anka Reuel", "Anka", "anka@cs.stanford.edu", "new co-author invite", "coauthor"),
    ("T28", "Max Lamparth", "Max", "lamparth@stanford.edu", "new co-author invite", "coauthor"),
    ("T29", "Varun Raj Madan", "Varun", "vmadan@stanford.edu", "new co-author invite", "varun"),
    ("V01", "Slava Naprienko", "Slava", "slava@vals.ai", "Vals colleague", ""),
    ("V02", "Nikil Ravi", "Nikil", "nikil@vals.ai", "Vals colleague", ""),
    # Brando, 11-17-2026: "vaibhav@vals.ai in case he didn't receive the ratings too. he should have." (V03 is Jacob, declined.)
    ("V04", "Vaibhav Mahajan", "Vaibhav", "vaibhav@vals.ai", "Vals colleague", ""),
]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def cohort_rows() -> list[tuple[str, str, str]]:
    cohort = json.loads(COHORT.read_text())
    layout = {**cohort["display_layout"], **cohort["layout_additions"]}
    return [(a["item_id"], layout[a["item_id"]]["task_folder"], layout[a["item_id"]]["candidate_file"])
            for a in cohort["artifacts"]]


def design(index: int) -> dict:
    return {"task_descending": (index // 2) % 2 == 1, "file_descending": index % 2 == 1,
            "start_task_offset": (7 * index) % 25}


def files_per_task() -> int:
    counts = {}
    for _, folder, _ in cohort_rows():
        counts[folder] = counts.get(folder, 0) + 1
    assert len(set(counts.values())) == 1, "Every task must have the same number of files"
    return next(iter(counts.values()))


def ordered_items(spec: dict) -> list[str]:
    """Same result as the Sheet requests: sort by task then file, then rotate whole tasks."""
    rows = sorted(cohort_rows(), key=lambda r: r[2], reverse=spec["file_descending"])
    rows = sorted(rows, key=lambda r: r[1], reverse=spec["task_descending"])  # stable: keeps file order
    cut = files_per_task() * spec["start_task_offset"]
    return [r[0] for r in rows[cut:] + rows[:cut]]


def sheet_requests(name: str, rater_id: str, spec: dict) -> list[dict]:
    end = 1 + len(cohort_rows())
    column = lambda c: {"sheetId": TEMPLATE_TAB_ID, "startRowIndex": 1, "endRowIndex": end,
                        "startColumnIndex": c, "endColumnIndex": c + 1}
    order = lambda descending: "DESCENDING" if descending else "ASCENDING"
    requests = [
        {"findReplace": {"find": "Brando Miranda", "replacement": name, "range": column(0),
                         "matchCase": True, "matchEntireCell": True}},
        {"findReplace": {"find": "A1", "replacement": rater_id, "range": column(1),
                         "matchCase": True, "matchEntireCell": True}},
        {"sortRange": {"range": {"sheetId": TEMPLATE_TAB_ID, "startRowIndex": 1, "endRowIndex": end,
                                 "startColumnIndex": 0, "endColumnIndex": 11},
                       "sortSpecs": [{"dimensionIndex": 3, "sortOrder": order(spec["task_descending"])},
                                     {"dimensionIndex": 4, "sortOrder": order(spec["file_descending"])}]}},
    ]
    if spec["start_task_offset"]:
        requests.append({"moveDimension": {"source": {"sheetId": TEMPLATE_TAB_ID, "dimension": "ROWS", "startIndex": 1,
                                                      "endIndex": 1 + files_per_task() * spec["start_task_offset"]},
                                           "destinationIndex": end}})
    return requests


def roster() -> list[dict]:
    people = []
    for index, (rater_id, name, greeting, email, group, opener) in enumerate(PEOPLE, 1):
        people.append({"rater_id": rater_id, "rater_name": name, "greeting": greeting, "email": email,
                       "group": group, "opener": opener, "design": design(index),
                       "sheet_title": f"VeriBench main rating sheet — {name} — {len(cohort_rows())} files"})
    return people


def plan() -> None:
    people = roster()
    assert len({p["rater_id"] for p in people}) == len(people) and len({p["email"] for p in people}) == len(people)
    (SEALED / "sheet_requests").mkdir(parents=True, exist_ok=True)
    for person in people:
        request = {"rater_id": person["rater_id"], "copy_file": {"fileId": TEMPLATE_SHEET_ID, "title": person["sheet_title"]},
                   "update_spreadsheet_requests": sheet_requests(person["rater_name"], person["rater_id"], person["design"])}
        (SEALED / "sheet_requests" / f"{person['rater_id']}.json").write_text(json.dumps(request, indent=1) + "\n")
    (SEALED / "ROSTER_FULL_TEAM.json").write_text(json.dumps(people, indent=1, ensure_ascii=False) + "\n")
    print(f"planned {len(people)} raters; request files in {SEALED / 'sheet_requests'}")


BRANDO_DRAFT = EXPERIMENT_DIR / "rating_task_packet/EMAIL_PATH_TO_GDOC.md"
DRAFT_SHEET_URL = f"https://docs.google.com/spreadsheets/d/{BRANDO_SHEET_ID}/edit"


EMAIL_FROM_DOC = SEALED / "EMAIL_FROM_DOC.json"


def brando_draft() -> dict:
    """Brando's own rater email: {"text": plain-text part, "html": HTML part with real nested lists}.

    The only editable copy is his Google Doc (EMAIL_PATH_TO_GDOC.md points to it). EMAIL_FROM_DOC.json in sealed/
    is a frozen render of one Doc revision, recorded with its revision ID; re-capture it after he edits the Doc.
    Brando, 11-17-2026: "STOP PUTTING GARBAGE LIKE THIS": only his text plus per-recipient fills (first name, personal
    Sheet link, his per-recipient opener); no notes, TLDR-end, assistant or drafted-with lines. HTML because Gmail
    collapses the leading spaces of a plain-text body, which removed his nested-list indentation ("tabs").
    """
    snap = json.loads(EMAIL_FROM_DOC.read_text())
    for part in ("text", "html"):
        assert snap[part].count(DRAFT_SHEET_URL) >= 1, f"{part}: Brando's draft changed shape; review"
        assert PACKET_DRIVE_URL in snap[part], f"{part}: the packet's Drive link is missing; the zip is no longer attached"
    assert snap["text"].count("Hi <Person Name>,") == 1 and snap["html"].count("<div>Hi &lt;Person Name&gt;,</div>") == 1
    return snap


def email_body(person: dict, sheet_url: str) -> str:
    body = brando_draft()["text"].replace(DRAFT_SHEET_URL, sheet_url)
    greeting = f"Hi {person['greeting']},"
    opener = "\n\n" + OPENERS[person["opener"]] if person["opener"] else ""  # his per-recipient opener, after the greeting
    return body.replace("Hi <Person Name>,", greeting + opener)


def email_html(person: dict, sheet_url: str) -> str:
    from html import escape
    body = brando_draft()["html"].replace(DRAFT_SHEET_URL, sheet_url)
    block = f"<div>Hi {escape(person['greeting'])},</div>"
    if person["opener"]:  # his per-recipient opener as its own paragraph, like the plain-text part
        block += f"\n<div><br></div>\n<div>{escape(OPENERS[person['opener']])}</div>"
    return body.replace("<div>Hi &lt;Person Name&gt;,</div>", block)


BRANDO = {"rater_id": "A1", "rater_name": "Brando Miranda", "greeting": "Brando", "opener": "",
          "email": "brandojazz@gmail.com",  # his main inbox; a BCC to the sending account lands in Sent only
          "design": {"task_descending": False, "file_descending": False, "start_task_offset": 0}}
TODAY = __import__("time").strftime("%m-%d-%Y")  # date of each action; the scheduler may finish on a later day


OLD_BUILDS = OUT / "builds"  # the 75-file builds of record, matched to the live Sheets on 11-14-2026


def row_order(rater_id: str) -> list[str]:
    if rater_id == "A1":
        return ordered_items(BRANDO["design"])
    old = OLD_BUILDS / rater_id / "ASSEMBLY_RECEIPT.json"
    if not old.exists():  # added after the 75-file round (V04, 11-17-2026): a hash-seeded uniformly random order
        return sorted((r[0] for r in cohort_rows()), key=lambda item: sha(f"added-rater-11-17-2026|{rater_id}|{item}".encode()))
    order = list(json.loads(old.read_text())["row_order"])
    salt = f"four-agent-insert-11-16-2026|{rater_id}|"  # fixed: the live Sheets were ordered with this salt
    new = sorted({r[0] for r in cohort_rows()} - set(order), key=lambda item: sha((salt + item).encode()))
    for item in new:  # sequential uniform insertion keeps the old order and randomizes the rest
        order.insert(int(sha((salt + item + "|position").encode()), 16) % (len(order) + 1), item)
    assert sorted(order) == sorted(r[0] for r in cohort_rows())
    return order


def registry() -> dict[str, str]:
    """rater_id -> live Sheet ID of record (created 11-14-2026)."""
    return {r: v["spreadsheet_id"] for r, v in json.loads(SHEET_REGISTRY.read_text()).items()}


def save_index(index: dict) -> None:
    BUILD_INDEX.write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n")


def already_sent() -> set[str]:
    """Raters whose packet email went out (send log); their delivered zip and index entry are never rebuilt."""
    log = SEALED / "SENT_100.json"
    return {r for r, v in (json.loads(log.read_text()) if log.exists() else {}).items() if v.get("status") == "sent"}


def build() -> None:
    sheets_by_rater = registry()
    index = json.loads(BUILD_INDEX.read_text()) if BUILD_INDEX.exists() else {}
    n = len(cohort_rows())
    sent = already_sent()
    for person in [BRANDO] + roster():
        rater_id = person["rater_id"]
        if rater_id in sent:
            continue  # delivered; keep its zip and index entry exactly as sent
        sheet_id = sheets_by_rater[rater_id]
        assert rater_id != "A1" or sheet_id == BRANDO_SHEET_ID
        url = f"https://docs.google.com/spreadsheets/d/{sheet_id}/edit"
        out = BUILDS / rater_id
        if not out.exists():
            bp.build_packet(COHORT, out, rater_name=person["rater_name"], rater_id=rater_id, sheet_url=url,
                            row_order=row_order(rater_id))
        receipt = json.loads((out / "ASSEMBLY_RECEIPT.json").read_text())
        assert receipt["sheet_url"] == url and receipt["artifact_count"] == n and receipt["task_count"] == 25
        assert receipt["row_order"] == row_order(rater_id), rater_id
        table = list(csv.reader(io.StringIO((out / "SHEET_TABLE.csv").read_text())))
        entry = index.setdefault(rater_id, {})
        if entry.get("expected_table_digest") not in (None, bp.table_digest(table)):
            entry["status"] = "HELD"  # the Sheet was matched against a different table; verify it again
        entry.update({"rater_name": person["rater_name"], "sheet_id": sheet_id, "sheet_url": url,
                      "expected_table_digest": bp.table_digest(table), "zip": receipt["archive_path"],
                      "zip_sha256": receipt["archive_sha256"]})
        entry.setdefault("status", receipt["status"])
        assert receipt["archive_sha256"] == PACKET_ZIP_SHA256, f"{rater_id}: zip differs from the shared Drive copy"
        DRAFTS_DIR.mkdir(exist_ok=True)
        draft = {"to": person["email"], "bcc": BCC, "subject": SUBJECT, "body": email_body(person, url), "html": email_html(person, url),
                 "packet_link": PACKET_DRIVE_URL, "packet_zip_sha256": receipt["archive_sha256"]}
        (DRAFTS_DIR / f"{rater_id}.json").write_text(json.dumps(draft, indent=1, ensure_ascii=False) + "\n")
    save_index(index)
    print(f"built {len(index)} packets of {n} files")


def sheets_session():
    from google.auth.transport.requests import AuthorizedSession, Request
    from google.oauth2.credentials import Credentials
    creds = Credentials.from_authorized_user_info(
        json.loads((Path.home() / "keys/gspread_authorized_user.json").read_text()))
    if not creds.valid:
        creds.refresh(Request())
    session = AuthorizedSession(creds)
    original = session.request

    def request(method, url, *args, **kwargs):
        # Back off on the per-minute quota (429: the request was not applied). Retry server errors only for
        # reads: a write that failed with 5xx may have been applied, so `sheets` must be rerun, and it rereads
        # the live table and inserts only rows still missing (batchUpdate is atomic), never replaying blindly.
        import time
        for wait in (0, 20, 40, 60, 90):
            time.sleep(wait)
            reply = original(method, url, *args, **kwargs)
            if not (reply.status_code == 429 or (reply.status_code >= 500 and method.upper() == "GET")):
                break
        reply.raise_for_status()
        return reply
    session.request = request
    return session


# Form version 7 (Brando, 11-18-2026: "yes add them but don't make them optional"): the rubric's quick checklist
# A-D as four required dropdown columns L:O after the version-6 columns (warm-up forms had a checklist and he liked it).
CHECKLIST_COLUMNS = ["A_key_gold_theorems_covered (Y/N)", "B_gold_pre_postconditions_preserved_or_strengthened (Y/N)",
                     "C_obvious_theorem_spam (Y/N)", "D_spam_handful_or_dominates (none/handful/dominates)"]
MAIN_COLUMNS = bp.COLUMNS[:5] + CHECKLIST_COLUMNS + bp.COLUMNS[5:]  # Brando, 11-18-2026: "the A-D should go before the final score"
ATTESTATION_HEADER = "ai_assisted_rating_attestation (AI help is allowed)"  # Brando, 11-18-2026
MAIN_COLUMNS = [ATTESTATION_HEADER if c == "ai_assisted_rating_attestation" else c for c in MAIN_COLUMNS]
SCORE = MAIN_COLUMNS.index("final_score_0_5")


def live_table(session, sheet_id: str) -> list[list[str]]:
    reply = session.get(f"{SHEETS_API}{sheet_id}/values/{TAB}!A1:O", params={"majorDimension": "ROWS"})
    return [row + [""] * (len(MAIN_COLUMNS) - len(row)) for row in reply.json().get("values", [])]


def sheets() -> None:
    """Insert the new rows where they belong in each live Sheet; existing rows and any entries move with them."""
    only = set(sys.argv[2:])
    index = json.loads(BUILD_INDEX.read_text())
    session = sheets_session()
    for rater_id, entry in index.items():
        if only and rater_id not in only:
            continue
        out = BUILDS / rater_id
        expected = list(csv.reader(io.StringIO((out / "SHEET_TABLE.csv").read_text())))
        meta = session.get(f"{SHEETS_API}{entry['sheet_id']}", params={"fields": "properties.title,sheets.properties"})
        meta.raise_for_status()
        meta = meta.json()
        tab = next(s["properties"] for s in meta["sheets"] if s["properties"]["title"] == TAB)
        now = live_table(session, entry["sheet_id"])
        assert now[0][:len(expected[0])] == expected[0], f"{rater_id}: header differs"
        now_ids, new_ids = [row[2] for row in now[1:]], [row[2] for row in expected[1:]]
        keep = set(now_ids)
        assert len(keep) == len(now_ids) and keep <= set(new_ids), f"{rater_id}: unexpected live rows"
        assert [i for i in new_ids if i in keep] == now_ids, f"{rater_id}: live order differs from the build"
        assert [row[:5] for row in now[1:]] == [row[:5] for row in expected[1:] if row[2] in keep], rater_id
        requests, inserted = [], 0
        for position, row in enumerate(expected[1:]):
            if row[2] in keep:
                continue
            at = 1 + position
            requests.append({"insertDimension": {"range": {"sheetId": tab["sheetId"], "dimension": "ROWS",
                                                           "startIndex": at, "endIndex": at + 1},
                                                 "inheritFromBefore": at > 1}})
            requests.append({"updateCells": {"start": {"sheetId": tab["sheetId"], "rowIndex": at, "columnIndex": 0},
                                             "rows": [{"values": [{"userEnteredValue": {"stringValue": v}}
                                                                  for v in row[:5]]}],
                                             "fields": "userEnteredValue"}})
            inserted += 1
        title = meta["properties"]["title"]
        new_title = re.sub(r"\b\d+ files\b", f"{len(new_ids)} files", title)
        if new_title != title:
            requests.append({"updateSpreadsheetProperties": {"properties": {"title": new_title}, "fields": "title"}})
        if requests:
            session.post(f"{SHEETS_API}{entry['sheet_id']}:batchUpdate", json={"requests": requests}).raise_for_status()
        after = live_table(session, entry["sheet_id"])
        responses = sum(any(cell.strip() for cell in row[5:11]) for row in after[1:])
        assert [row[:5] for row in after] == [row[:5] for row in expected], f"{rater_id}: identifiers differ after insert"
        entry.update({"rows_inserted": inserted, "live_title": new_title, "responses_at_check": responses})
        if responses == 0:
            bp.verify_sheet_digest(out, bp.table_digest(after), len(after),
                                   f"Sheets API read of {TAB}!A1:K after inserting rows, {TODAY}")
            entry["status"] = "BUILT_SHEET_MATCHED_NOT_SENT"
        else:
            entry["status"] = "SHEET_IDENTIFIERS_MATCHED_WITH_RESPONSES"
        save_index(index)
        print(rater_id, entry["status"], f"inserted={inserted}", f"responses={responses}", new_title)


FORM_V5_COLUMNS = bp.COLUMNS[:9] + ["rationale", "problem_note"]  # main Sheets before 11-17-2026
FORM_VERSION = json.loads((HERE.parents[1] / "RATING_FORM_SCHEMA.json").read_text())["version"]


def sheet_layout(session, sheet_id: str) -> dict:
    """Tab ID, A:K widths and hidden flags, and the row-2 data validation of each column."""
    reply = session.get(f"{SHEETS_API}{sheet_id}", params={
        "ranges": f"{TAB}!A1:K2",
        "fields": "sheets(properties(sheetId,title),data(columnMetadata(pixelSize,hiddenByUser),rowData(values(dataValidation))))"})
    sheet = reply.json()["sheets"][0]
    data = sheet["data"][0]
    columns = data.get("columnMetadata", [])
    second = (data.get("rowData", [{}, {}]) + [{}, {}])[1].get("values", [])
    return {"tab_id": sheet["properties"]["sheetId"],
            "widths": [c.get("pixelSize") for c in columns], "hidden": [bool(c.get("hiddenByUser")) for c in columns],
            "validation": [json.dumps((second[i] if i < len(second) else {}).get("dataValidation"), sort_keys=True)
                           for i in range(11)]}


def rationale_last() -> None:
    """Brando, 11-17-2026: "Let's just put the rationale at the end and a (optional) column name. Go!"

    Moves column J (`rationale`) after K (`problem_note`) in each live main Sheet with moveDimension, so its width,
    format and validation travel with it, and renames the header to `rationale (optional)`. Refuses any Sheet with a
    response in F:K; skips Sheets already moved. Checks identifiers, widths, hidden columns and validation afterwards.
    """
    only = set(sys.argv[2:])
    index = json.loads(BUILD_INDEX.read_text())
    session = sheets_session()
    swap = lambda values: values[:9] + [values[10], values[9]] + values[11:]  # noqa: E731
    for rater_id, entry in index.items():
        if only and rater_id not in only:
            continue
        sheet_id = entry["sheet_id"]
        table = live_table(session, sheet_id)
        if table[0] == bp.COLUMNS:
            print(rater_id, "already in form version 6")
            continue
        assert table[0] == FORM_V5_COLUMNS, f"{rater_id}: unexpected header {table[0]}"
        responses = sum(any(cell.strip() for cell in row[5:11]) for row in table[1:])
        assert responses == 0, f"{rater_id}: {responses} rows have responses; not moving any column"
        before = sheet_layout(session, sheet_id)
        tab = before["tab_id"]
        session.post(f"{SHEETS_API}{sheet_id}:batchUpdate", json={"requests": [
            {"moveDimension": {"source": {"sheetId": tab, "dimension": "COLUMNS", "startIndex": 9, "endIndex": 10},
                               "destinationIndex": 11}},
            {"updateCells": {"start": {"sheetId": tab, "rowIndex": 0, "columnIndex": 10},
                             "rows": [{"values": [{"userEnteredValue": {"stringValue": bp.COLUMNS[10]}}]}],
                             "fields": "userEnteredValue"}}]}).raise_for_status()
        after_table, after = live_table(session, sheet_id), sheet_layout(session, sheet_id)
        assert after_table[0] == bp.COLUMNS, f"{rater_id}: header after move {after_table[0]}"
        assert [row[:5] for row in after_table] == [row[:5] for row in table], f"{rater_id}: identifiers changed"
        assert not any(cell.strip() for row in after_table[1:] for cell in row[5:11]), rater_id
        assert after["widths"] == swap(before["widths"]) and after["hidden"] == swap(before["hidden"]), rater_id
        assert after["hidden"][1:4] == [True, True, True], f"{rater_id}: B:D not hidden"
        assert after["validation"] == swap(before["validation"]), f"{rater_id}: validation changed"
        entry["form_v6_move"] = {"date": TODAY, "utc": now_utc(), "tab_id": tab, "old_header": table[0],
                                 "new_header": after_table[0], "rows": len(after_table) - 1,
                                 "widths_before": before["widths"], "widths_after": after["widths"]}
        save_index(index)
        print(rater_id, "moved; widths", after["widths"][5:11], "hidden B:D kept; validation kept")


def verify() -> None:
    """Fallback input: sealed/LIVE_DIGESTS.json {sheet_id: 'digest:rows:rows_with_responses'} read in the owner's browser."""
    observed = json.loads((SEALED / "LIVE_DIGESTS.json").read_text())
    index = json.loads(BUILD_INDEX.read_text())
    bad = []
    for rater_id, entry in index.items():
        digest, rows, responses = observed.get(entry["sheet_id"], "::").split(":")
        try:
            assert responses == "0", "live Sheet already has responses"
            bp.verify_sheet_digest(BUILDS / rater_id, digest, int(rows or 0),
                                   "gviz CSV read of the Ratings tab in the owner's signed-in browser")
            entry["status"] = "BUILT_SHEET_MATCHED_NOT_SENT"
        except (AssertionError, ValueError) as error:
            bad.append((rater_id, str(error)))
            entry["status"] = "HELD"
    save_index(index)
    print(f"matched {len(index) - len(bad)} of {len(index)}; held: {bad}")


def message_for(rater_id: str):
    from email.message import EmailMessage
    from email.utils import make_msgid
    draft = json.loads((DRAFTS_DIR / f"{rater_id}.json").read_text())
    assert draft["packet_link"] == PACKET_DRIVE_URL and draft["packet_zip_sha256"] == PACKET_ZIP_SHA256, rater_id
    assert PACKET_DRIVE_URL in draft["body"] and PACKET_DRIVE_URL in draft["html"], rater_id
    message = EmailMessage()
    message["From"] = "Brando Miranda <brandojazz@gmail.com>"
    message["To"], message["Bcc"], message["Subject"] = draft["to"], ", ".join(draft["bcc"]), draft["subject"]
    message["Message-ID"] = make_msgid(domain="gmail.com")
    message.set_content(draft["body"])
    message.add_alternative(draft["html"], subtype="html")  # no attachment: the packet is the Drive link in the text
    return draft, message


def trash_draft(box, uid: bytes) -> None:
    """Move one Drafts message to Trash. Gmail can refuse a MOVE transiently (11-17-2026: T03's old draft, UID 12801),
    so retry, and count it done once the UID is no longer in Drafts."""
    import time
    for attempt in range(4):
        status, reply = box.uid("MOVE", uid, "[Gmail]/Trash")
        box.select("[Gmail]/Drafts")
        if status == "OK" or not box.uid("FETCH", uid, "(UID)")[1][0]:
            return
        time.sleep(10 * (attempt + 1))
    raise AssertionError(("could not move draft to Trash", uid, status, reply))


def drafts() -> None:
    """Replace each rater's unsent draft (same recipient and subject) with the current one. Nothing is sent."""
    import imaplib
    import time
    password = (Path.home() / "keys/gmail_app_password.txt").read_text().strip()
    index = json.loads(BUILD_INDEX.read_text())
    log_path = DRAFTS_LOG
    saved = json.loads(log_path.read_text()) if log_path.exists() else {}
    with imaplib.IMAP4_SSL("imap.gmail.com") as box:
        box.login("brandojazz@gmail.com", password)
        box.select("[Gmail]/Drafts")
        sent = already_sent()
        for rater_id in sorted(sent - {"A1"}):  # a sent rater's leftover draft could go out twice; move it to Trash
            to = index[rater_id].get("to") or json.loads((DRAFTS_DIR / f"{rater_id}.json").read_text())["to"]
            leftover = [u for s in SUBJECTS for u in box.uid("SEARCH", None, "TO", f'"{to}"', "SUBJECT", f'"{s}"')[1][0].split()]
            for uid in leftover:
                trash_draft(box, uid)
            if leftover:
                saved[rater_id] = {**saved.get(rater_id, {}), "sent": True, "retired_draft_uids": [u.decode() for u in leftover],
                                   "retired": TODAY}
                log_path.write_text(json.dumps(saved, indent=1) + "\n")
            box.select("[Gmail]/Drafts")
        for path in sorted(DRAFTS_DIR.glob("*.json")):
            rater_id = path.stem
            if rater_id in sent:
                continue
            spec = json.loads(path.read_text())
            fingerprint = sha(json.dumps({k: spec[k] for k in ("to", "bcc", "subject", "body", "html", "packet_link")},
                                         sort_keys=True).encode())
            if rater_id == "A1" or saved.get(rater_id, {}).get("fingerprint") == fingerprint:
                continue  # this exact draft is already in Gmail
            assert index[rater_id]["status"] == "BUILT_SHEET_MATCHED_NOT_SENT", rater_id
            draft, message = message_for(rater_id)
            queries = [("TO", f'"{draft["to"]}"', "SUBJECT", f'"{s}"') for s in SUBJECTS]
            mine = ("HEADER", "Message-ID", message["Message-ID"])
            reply = [b""]
            for attempt in range(3):
                # Gmail can answer "System Error (Failure)" yet store the draft, so confirm by Message-ID.
                status, reply = box.append("[Gmail]/Drafts", "\\Draft", imaplib.Time2Internaldate(time.time()),
                                           message.as_bytes())
                box.select("[Gmail]/Drafts")
                new = box.uid("SEARCH", None, *mine)[1][0].split()
                if new:
                    break
                time.sleep(10 * (attempt + 1))
            assert len(new) == 1, (rater_id, status, reply)
            found = [u for q in queries for u in box.uid("SEARCH", None, *q)[1][0].split()]
            old = [uid for uid in found if uid not in new]
            for uid in old:
                trash_draft(box, uid)
            box.select("[Gmail]/Drafts")
            now = [u for q in queries for u in box.uid("SEARCH", None, *q)[1][0].split()]
            assert now == new, (rater_id, now)
            saved[rater_id] = {"to": draft["to"], "zip_sha256": draft["packet_zip_sha256"], "packet_link": draft["packet_link"],
                               "fingerprint": fingerprint,
                               "message_id": message["Message-ID"], "draft_uid": new[0].decode(),
                               "append_reply": reply[0].decode(errors="replace") if reply and reply[0] else "",
                               "replaced_draft_uids": [u.decode() for u in old], "sent": False, "saved": TODAY}
            log_path.write_text(json.dumps(saved, indent=1) + "\n")
    print(f"{len(saved)} unsent drafts are in Gmail Drafts; nothing was sent")


def ensure_in_inbox(password: str, message_id: str) -> str:
    """Confirm the self-sent packet shows in brandojazz@gmail.com's Inbox; add the Inbox label if Gmail kept it in Sent only."""
    import imaplib
    import time
    with imaplib.IMAP4_SSL("imap.gmail.com") as box:
        box.login("brandojazz@gmail.com", password)
        for _ in range(12):
            box.select("INBOX", readonly=True)
            if box.uid("SEARCH", None, "HEADER", "Message-ID", message_id)[1][0].split():
                return "in Inbox"
            box.select('"[Gmail]/All Mail"')
            found = box.uid("SEARCH", None, "HEADER", "Message-ID", message_id)[1][0].split()
            if found:
                assert box.uid("COPY", found[-1], "INBOX")[0] == "OK"  # Gmail: copying to INBOX adds the Inbox label
                box.select("INBOX", readonly=True)
                if box.uid("SEARCH", None, "HEADER", "Message-ID", message_id)[1][0].split():
                    return "Inbox label added"
            time.sleep(5)
    raise AssertionError("Sent, but not found in brandojazz@gmail.com within a minute")


def send_lock():
    """Exclusive, non-blocking lock so two processes can never send at the same time."""
    import fcntl
    handle = open(SEALED / "SEND.lock", "w")
    try:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit("Another send is running; refusing to send concurrently")
    return handle  # keep a reference; the lock is released when the process exits


def send_a1() -> None:
    """Send Brando's own packet to Brando (requested in chat 11-16-2026). Sends to nobody else."""
    import smtplib
    lock = send_lock()  # noqa: F841
    index = json.loads(BUILD_INDEX.read_text())
    entry = index["A1"]
    assert entry["status"] in ("BUILT_SHEET_MATCHED_NOT_SENT", "SHEET_IDENTIFIERS_MATCHED_WITH_RESPONSES"), entry["status"]
    # Brando, 11-17-2026: no notes in rater emails ("STOP PUTTING GARBAGE LIKE THIS"); the body is his draft only.
    assert len(sys.argv) == 2, "send-a1 takes no note: the email is Brando's draft text only"
    draft, message = message_for("A1")
    recipients = sorted({draft["to"], *draft["bcc"]})
    assert all(r in ("brando9@stanford.edu", "brandojazz@gmail.com", "brando.science@gmail.com") for r in recipients)
    assert draft["to"] == "brandojazz@gmail.com", "Rebuild A1's draft so it goes to brandojazz@gmail.com"
    password = (Path.home() / "keys/gmail_app_password.txt").read_text().strip()
    with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
        smtp.login("brandojazz@gmail.com", password)
        refused = smtp.send_message(message, to_addrs=recipients)
    assert not refused, refused
    inbox = ensure_in_inbox(password, message["Message-ID"])
    if entry.get("sent_to_self"):  # sealed/ is not in Git, so keep each earlier self-send receipt here
        entry.setdefault("sent_to_self_earlier", []).append(entry["sent_to_self"])
    entry["sent_to_self"] = {"date": TODAY, "to": draft["to"], "bcc": draft["bcc"],
                             "message_id": message["Message-ID"], "zip_sha256": draft["packet_zip_sha256"],
                             "packet_link": draft["packet_link"],
                             "brandojazz_inbox": inbox}
    save_index(index)
    print("sent A1 to", recipients, message["Message-ID"], "|", inbox)


SENT_LOG = SEALED / "SENT_100.json"
# Brando (chat, 11-16-2026): "don't send anything to the team until I do my ratings". `send --confirm` refuses while
# this is set. Lifted 11-17-2026 on Brando's explicit go: "basically I think we are ready to send the request to raters
# now. Go!" and, for the Drive-link version, "Instead create a zip copy to my gdrive and send that linke ... Go!".
TEAM_SEND_HOLD = ""
# People Brando cleared by name while the hold stands; `send --confirm` may send only these until the hold is lifted.
HOLD_EXCEPTIONS = {
    "T05": "Brando, 11-17-2026: \"can you send this now to nikil and sri too. Please.\"",
    "V02": "Brando, 11-17-2026: \"can you send this now to nikil and sri too. Please.\"",
    "T02": "Brando, 11-17-2026: \"Can we send the packet to Yegor too please?\"",
}
SUBJECT_QUERY = '"VeriBench human-rating main rating task"'
EXPERIMENT = REPO / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026"
STATUS_START, STATUS_END = "<!-- grading-status:start -->", "<!-- grading-status:end -->"
ROLE = {"author": "VeriBench co-author", "author (extra-only designation preserved)": "VeriBench co-author (extra_only)",
        "new co-author invite": "New co-author invitee", "Vals colleague": "Vals AI rater"}


def now_utc() -> str:
    from datetime import datetime, timezone
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def send() -> None:
    """The one send path: send each rater's saved Gmail draft as it stands, then move that draft to Trash.

    Dry run unless --confirm; target --all or listed rater IDs. Anyone who already has this email in
    Sent Mail is skipped, so a draft sent by hand from Gmail is never sent twice.
    """
    import email
    import imaplib
    import smtplib
    from email import policy
    from email.utils import formatdate
    args = sys.argv[2:]
    confirm = "--confirm" in args
    named = [a for a in args if not a.startswith("--")]
    if confirm and TEAM_SEND_HOLD and ("--all" in args or not named or not set(named) <= set(HOLD_EXCEPTIONS)):
        raise SystemExit(f"Team emails are on hold ({TEAM_SEND_HOLD}); only {sorted(HOLD_EXCEPTIONS)} may be sent by name. "
                         "Nothing was sent")
    lock = send_lock()  # noqa: F841
    index = json.loads(BUILD_INDEX.read_text())
    saved = json.loads(DRAFTS_LOG.read_text())
    targets = sorted(saved) if "--all" in args else [a for a in args if not a.startswith("--")]
    assert targets and set(targets) <= set(saved), "Name rater IDs or --all"
    sent_log = json.loads(SENT_LOG.read_text()) if SENT_LOG.exists() else {}
    password = (Path.home() / "keys/gmail_app_password.txt").read_text().strip()
    smtp = None
    with imaplib.IMAP4_SSL("imap.gmail.com") as box:
        box.login("brandojazz@gmail.com", password)
        try:
            for rater_id in targets:
                entry, record = index[rater_id], saved[rater_id]
                to = record["to"]
                prior = sent_log.get(rater_id, {})
                box.select('"[Gmail]/Sent Mail"', readonly=True)
                by_id = bool(prior.get("message_id")) and bool(
                    box.uid("SEARCH", None, "HEADER", "Message-ID", prior["message_id"])[1][0].split())
                by_subject = any(box.uid("SEARCH", None, "TO", f'"{to}"', "SUBJECT", f'"{s}"')[1][0].split() for s in SUBJECTS)
                if prior.get("status", "sent") == "sent" and prior or by_id or by_subject:
                    if prior.get("status") != "sent":
                        sent_log[rater_id] = {**prior, "status": "sent", "reconciled_utc": now_utc()}
                        SENT_LOG.write_text(json.dumps(sent_log, indent=1) + "\n")
                    print(f"{rater_id}: already sent, skipped")
                    continue
                box.select("[Gmail]/Drafts")
                uids = [u for s in SUBJECTS for u in box.uid("SEARCH", None, "TO", f'"{to}"', "SUBJECT", f'"{s}"')[1][0].split()]
                assert len(uids) == 1, f"{rater_id}: expected one draft, found {len(uids)}"
                message = email.message_from_bytes(box.uid("FETCH", uids[0], "(BODY.PEEK[])")[1][0][1], policy=policy.SMTP)
                assert not list(message.iter_attachments()), f"{rater_id}: draft has an attachment; the packet is a Drive link"
                assert entry["zip_sha256"] == PACKET_ZIP_SHA256 == record["zip_sha256"], f"{rater_id}: not the shared zip"
                assert message["To"].strip().lower() == to.lower() and entry["status"] == "BUILT_SHEET_MATCHED_NOT_SENT"
                for part in ("plain", "html"):
                    content = message.get_body((part,)).get_content()
                    assert entry["sheet_url"] in content, f"{rater_id}: Sheet link missing ({part})"
                    assert PACKET_DRIVE_URL in content, f"{rater_id}: packet Drive link missing ({part})"
                recipients = sorted({to, *(a.strip() for a in str(message["Bcc"] or "").split(",") if a.strip())})
                if not confirm:
                    print(f"[dry run] {rater_id} {entry['rater_name']} -> {', '.join(recipients)}")
                    continue
                if smtp is None:
                    smtp = smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=120)
                    smtp.login("brandojazz@gmail.com", password)
                if not message["Date"]:
                    message["Date"] = formatdate(localtime=True)
                # Record the attempt first: if the process dies mid-send, the next run finds this
                # Message-ID in Sent Mail (or not) before deciding, instead of sending blindly again.
                sent_log[rater_id] = {"status": "sending", "started_utc": now_utc(), "to": to,
                                      "message_id": message["Message-ID"], "zip_sha256": entry["zip_sha256"],
                                      "packet_link": PACKET_DRIVE_URL}
                SENT_LOG.write_text(json.dumps(sent_log, indent=1) + "\n")
                refused = smtp.send_message(message, to_addrs=recipients)  # Bcc header is stripped on send
                assert not refused, refused
                box.uid("MOVE", uids[0], "[Gmail]/Trash")
                sent_log[rater_id] = {**sent_log[rater_id], "status": "sent", "sent_utc": now_utc(),
                                      "bcc": sorted(set(recipients) - {to})}
                SENT_LOG.write_text(json.dumps(sent_log, indent=1) + "\n")
                print(f"sent {rater_id} {entry['rater_name']} -> {to}")
        finally:
            if smtp is not None:
                smtp.quit()
    print("dry run only; nothing was sent" if not confirm else
          f"{sum(v.get('status', 'sent') == 'sent' for v in sent_log.values())} sent in total")


# Earlier resends (11-17-2026, 16:12 PT) attached slim zips from sealed/builds_100_native_resend_11-17-2026/ under
# Brando's "Resend to nikil yegor sri brando please."; their records in SENT_100.json keep that quote.
RESEND_AUTHORIZED_BY = ('Brando, chat 11-17-2026: "cuz stanford removes the zip file attached. Instead create a zip copy '
                        'to my gdrive and send that linke"')


def resend() -> None:
    """Send the current email (Brando's Doc, frozen in EMAIL_FROM_DOC.json, packet as a Drive link) again.

    Only raters in HOLD_EXCEPTIONS and A1 are allowed; dry run unless --confirm. Nothing is attached (see PACKET_DRIVE_URL).
    Each send is recorded (SENT_100.json "resends", or A1's sent_to_self in the index) with Brando's request:
    pass his words as --quote="..." (default RESEND_AUTHORIZED_BY).
    """
    import smtplib
    from email.message import EmailMessage
    from email.utils import formatdate, make_msgid
    args = sys.argv[2:]
    confirm = "--confirm" in args
    quote = next((a.split("=", 1)[1] for a in args if a.startswith("--quote=")), RESEND_AUTHORIZED_BY)
    targets = [a for a in args if not a.startswith("--")]
    allowed = set(HOLD_EXCEPTIONS) | {"A1"}
    assert targets and set(targets) <= allowed, f"Name raters Brando cleared: {sorted(allowed)}"
    lock = send_lock()  # noqa: F841
    index = json.loads(BUILD_INDEX.read_text())
    sent_log = json.loads(SENT_LOG.read_text()) if SENT_LOG.exists() else {}
    people = {p["rater_id"]: p for p in roster()}
    people["A1"] = BRANDO
    password = (Path.home() / "keys/gmail_app_password.txt").read_text().strip()
    snap = brando_draft()
    ready = []
    for rid in targets:
        person, entry = people[rid], index[rid]
        url = entry["sheet_url"]
        message = EmailMessage()
        message["From"] = "Brando Miranda <brandojazz@gmail.com>"
        message["To"], message["Bcc"], message["Subject"] = person["email"], ", ".join(BCC), SUBJECT
        message["Date"], message["Message-ID"] = formatdate(localtime=True), make_msgid(domain="gmail.com")
        message.set_content(email_body({**person, "opener": ""}, url))
        message.add_alternative(email_html({**person, "opener": ""}, url), subtype="html")
        for part in ("plain", "html"):
            content = message.get_body((part,)).get_content()
            assert url in content and PACKET_DRIVE_URL in content and "START_HERE" not in content, (rid, part)
        assert not list(message.iter_attachments()), rid
        ready.append((rid, person, message))
        print(f"{'' if confirm else '[dry run] '}{rid} {person['rater_name']} -> {person['email']} bcc {', '.join(BCC)} | {SUBJECT} | "
              f"Drive link, zip {PACKET_ZIP_SHA256[:12]} | doc revision {snap['doc_revision_id'][:12]}")
    if not confirm:
        print("dry run only; nothing was sent")
        return
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=120) as smtp:
        smtp.login("brandojazz@gmail.com", password)
        for rid, person, message in ready:
            refused = smtp.send_message(message, to_addrs=sorted({person["email"], *BCC}))
            assert not refused, refused
            record = {"utc": now_utc(), "message_id": message["Message-ID"], "to": person["email"], "bcc": BCC, "subject": SUBJECT,
                      "packet_link": PACKET_DRIVE_URL, "zip_sha256": PACKET_ZIP_SHA256, "doc_revision_id": snap["doc_revision_id"],
                      "authorized_by": quote}
            if rid == "A1":
                entry = index["A1"]
                entry.setdefault("sent_to_self_earlier", []).append(entry.get("sent_to_self", {}))
                entry["sent_to_self"] = {**record, "date": TODAY, "brandojazz_inbox": ensure_in_inbox(password, message["Message-ID"])}
                save_index(index)
            else:
                sent_log.setdefault(rid, {}).setdefault("resends", []).append(record)
                SENT_LOG.write_text(json.dumps(sent_log, indent=1) + "\n")
            print(f"sent {rid} {person['rater_name']} -> {person['email']} {message['Message-ID']}")


def main_csv_entry(manifest: dict, rater_id: str) -> dict:
    found = [f for f in manifest["files"] if f["rater_id"] == rater_id and f["packet"] == "native_main"]
    assert len(found) == 1, rater_id
    return found[0]


def export() -> None:
    """Write each live main Sheet's exact table to ratings/ and refresh RAW_MANIFEST.json and SUMMARY.json."""
    ratings = EXPERIMENT / "ratings"
    manifest_path, summary_path = ratings / "RAW_MANIFEST.json", ratings / "SUMMARY.json"
    manifest, summary = json.loads(manifest_path.read_text()), json.loads(summary_path.read_text())
    index = json.loads(BUILD_INDEX.read_text())
    session = sheets_session()
    scored = {}
    for rater_id, entry in index.items():
        table = live_table(session, entry["sheet_id"])
        assert table[0] == MAIN_COLUMNS and all(row[1] == rater_id for row in table[1:]), rater_id
        record = main_csv_entry(manifest, rater_id)
        buffer = io.StringIO()
        csv.writer(buffer, lineterminator="\n").writerows(add_source_label(table, "main"))  # Sheet columns plus source_label
        data = buffer.getvalue().encode()
        (ratings / record["filename"]).write_bytes(data)
        numeric = sum(row[SCORE].strip() in {"0", "1", "2", "3", "4", "5"} for row in table[1:])
        not_applicable = sum(row[SCORE].strip().upper() == "N/A" for row in table[1:])
        scored[rater_id] = numeric
        record.update({
            "columns": table[0], "csv_columns": [*table[0], "source_label"], "source_label": "main", "form_version": FORM_VERSION,
            "url": entry["sheet_url"], "spreadsheet_id": entry["sheet_id"], "range": f"{TAB}!A1:O{len(table)}",
            "assigned_rows": len(table) - 1, "rows": len(table) - 1, "numeric_ratings": numeric,
            "not_applicable_rows": not_applicable, "sha256": sha(data),
            "source_readback_sha256": sha(json.dumps(table, ensure_ascii=False, separators=(",", ":")).encode()),
            # T05's and V02's delivered builds moved to sealed/delivered_direct_11-17-2026/ without their receipts: keep the hash on record
            "assembly_receipt_sha256": sha(receipt.read_bytes()) if (receipt := BUILDS / rater_id / "ASSEMBLY_RECEIPT.json").exists()
                                       else record["assembly_receipt_sha256"],
            "status": "prepared blank form, not a completed observation" if numeric + not_applicable == 0
                      else "live table; participant responses preserved as entered"})
    manifest["numeric_observations"] = sum(f.get("numeric_ratings", 0) for f in manifest["files"])
    manifest["not_applicable_rows"] = sum(f.get("not_applicable_rows", 0) for f in manifest["files"])
    manifest["checked_date"], manifest["recorded_utc"] = TODAY, now_utc()
    change = {"100": "25 rows per Sheet for Gemini 4 Argon (Terminus 2, high effort; planned Google cells), inserted in place",
              "100_native": "Rows unchanged; 56 files' contents replaced by native-harness runs (Grok 4.7 in Grok CLI x25, "
                            "Gemini 4 Argon in Antigravity CLI x25, Claude Fable 5.1 in Claude Code x6)"}[ROUND_TAG]
    commitment = {"100": "COHORT_100_COMMITMENT.json", "100_native": "COHORT_100_NATIVE_COMMITMENT.json"}[ROUND_TAG]
    revision = {"date": TODAY, "round": ROUND_TAG, "artifacts": len(cohort_rows()), "tasks": 25,
                "agents_per_task": files_per_task(), "added": change,
                "sheets_verified": len(index), "main_numeric_observations": sum(scored.values()),
                "emails_sent": "A1 to self only" if not SENT_LOG.exists() else f"A1 to self + {len(json.loads(SENT_LOG.read_text()))}",
                "cohort_commitment": "../../../research_artifacts/09_human_rating_collection/preparation_11-09-2026/"
                                     f"full_team_11-14-2026/{commitment}"}
    manifest[f"full_team_{ROUND_TAG}_revision"] = revision  # one record per round; earlier rounds are kept
    summary["checked_date"] = TODAY
    summary[f"full_team_{ROUND_TAG}_sync"] = {k: revision[k] for k in ("date", "artifacts", "tasks", "agents_per_task",
                                                              "sheets_verified", "main_numeric_observations", "emails_sent")}
    manifest_path.write_text(json.dumps(manifest, indent=1, ensure_ascii=False) + "\n")
    summary_path.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n")
    print(f"exported {len(index)} main Sheets; numeric main ratings: {sum(scored.values())}")


def review() -> None:
    """Write the review page of all 31 team emails from the current drafts, so it never drifts from what Gmail holds."""
    index = json.loads(BUILD_INDEX.read_text())
    saved = json.loads(DRAFTS_LOG.read_text()) if DRAFTS_LOG.exists() else {}
    sent_log = json.loads(SENT_LOG.read_text()) if SENT_LOG.exists() else {}
    rows = []
    for person in roster():
        rater_id = person["rater_id"]
        if sent_log.get(rater_id, {}).get("status") == "sent":
            rows.append(f"| `{rater_id}` | {person['rater_name']} | {person['email']} | {person['greeting']} | "
                        f"{person['opener'] or '—'} | [Sheet]({index[rater_id]['sheet_url']}) | "
                        f"sent {sent_log[rater_id].get('sent_utc', '')} |")
            continue
        draft = json.loads((DRAFTS_DIR / f"{rater_id}.json").read_text())
        assert draft["body"] == email_body(person, index[rater_id]["sheet_url"]), f"{rater_id}: draft differs from the template"
        assert draft["packet_zip_sha256"] == index[rater_id]["zip_sha256"] == saved.get(rater_id, {}).get("zip_sha256"), \
            f"{rater_id}: the Gmail draft does not hold the current packet; run `drafts` first"
        assert saved[rater_id].get("packet_link") == draft["packet_link"] == PACKET_DRIVE_URL, f"{rater_id}: run `drafts` first"
        rows.append(f"| `{rater_id}` | {person['rater_name']} | {person['email']} | {person['greeting']} | "
                    f"{person['opener'] or '—'} | [Sheet]({index[rater_id]['sheet_url']}) | `{draft['packet_zip_sha256'][:12]}` |")
    sent = sum(v.get("status", "sent") == "sent" for v in sent_log.values())
    page = "\n".join([
        f"# Review all 31 rating emails ({len(cohort_rows())}-file packets), {TODAY}", "",
        f"**TLDR:** These are the 31 Gmail drafts (one per rater, `{sent}` sent). Every email is the common text below with "
        f"the rater's first name, personal Sheet link, the Google Drive link to the shared packet `.zip` "
        f"({len(cohort_rows())} agent files; nothing attached, since Stanford's mail filter strips .zip files) and, for some, a "
        "one-paragraph opener. Send only with `python3 experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/"
        "support/scripts/native_packet_generation/build_full_team_packets.py send --confirm --all` after Brando's yes; it sends "
        "each draft as it stands in Gmail (so edits there are kept), skips anyone already sent and moves the sent draft to Trash. "
        "The email text itself lives only in Brando's Google Doc: "
        "<https://docs.google.com/document/d/1KJQHxA-pSMxr31ZPMq8dI5bWPjnObQ2CHlQZ6g5r3f8/edit?tab=t.bmtmw71ddlms>. "
        f"Generated by `build_full_team_packets.py review` from round `{ROUND_TAG}`.", "",
        *([f"**On hold:** {TEAM_SEND_HOLD}. `send --confirm` refuses until the hold is cleared.", ""]
          if TEAM_SEND_HOLD else []),
        f"- **Subject:** {SUBJECT}", "- **From:** Brando Miranda <brandojazz@gmail.com>",
        f"- **BCC (every email):** {', '.join(BCC)}", "",
        f"**Email text:** only in Brando's Google Doc (sent as HTML with nested lists, from the frozen render "
        f"`sealed/EMAIL_FROM_DOC.json`, Doc revision `{brando_draft()['doc_revision_id'][:16]}…`).", "",
        "## Openers (inserted after the greeting)", "",
        *[f"- **{name}:** {text}" for name, text in OPENERS.items()], "",
        "## Per-rater differences", "",
        f"- **Packet (every email):** {PACKET_DRIVE_URL} (zip SHA-256 `{PACKET_ZIP_SHA256}`)", "",
        "| ID | Rater | To | Greeting | Opener | Personal Sheet | Linked zip SHA-256 (first 12), or sent |",
        "| --- | --- | --- | --- | --- | --- | --- |", *rows, "",
        "Varun's opener leaves out the dictated clause about Anthropic (\"not interested\" vs \"now interested\" was "
        "ambiguous); add it in his Gmail draft if wanted.", ""])
    (OUT / f"REVIEW_ALL_31_EMAILS_{TODAY}.md").write_text(page)
    print(f"wrote {OUT / f'REVIEW_ALL_31_EMAILS_{TODAY}.md'} ({len(rows)} raters)")


def pacific(utc_iso: str) -> str:
    """'2026-11-18T02:31:05+00:00' -> '11-17-2026 18:31 PT' (prose dates are MM-DD-YYYY)."""
    from datetime import datetime
    from zoneinfo import ZoneInfo
    return datetime.fromisoformat(utc_iso).astimezone(ZoneInfo("America/Los_Angeles")).strftime("%m-%d-%Y %H:%M PT")


def status() -> None:
    """Who is grading: one row per rater with live progress, written into the experiment README."""
    index = json.loads(BUILD_INDEX.read_text())
    saved_path = DRAFTS_LOG
    saved = json.loads(saved_path.read_text()) if saved_path.exists() else {}
    sent_log = json.loads(SENT_LOG.read_text()) if SENT_LOG.exists() else {}
    manifest = json.loads((EXPERIMENT / "ratings/RAW_MANIFEST.json").read_text())
    warmup = {f["rater_id"]: f for f in manifest["files"] if f["packet"] == "warmup"}
    people = {p["rater_id"]: p for p in [BRANDO] + roster()}
    session = sheets_session()
    rows, total = [], 0
    for rater_id, entry in index.items():
        table = live_table(session, entry["sheet_id"])
        done = sum(row[SCORE].strip() != "" for row in table[1:])
        total += done
        if rater_id == "A1":
            earlier = SEALED / "BUILD_INDEX_100.json"  # the first 100-file packet (Terminus 2 Grok and Gemini files)
            before = json.loads(earlier.read_text())["A1"].get("sent_to_self") if earlier != BUILD_INDEX else None
            mail = (f"emailed to self {entry['sent_to_self']['date']}" if entry.get("sent_to_self") else
                    "current packet not emailed yet" + (f"; earlier 100-file packet emailed {before['date']}" if before else ""))
        elif rater_id in sent_log and sent_log[rater_id].get("status", "sent") == "sent":
            mail = f"sent {pacific(sent_log[rater_id]['sent_utc'])}"
            if any(r.get("packet_link") for r in sent_log[rater_id].get("resends", [])):
                mail += f"; Drive-link copy {pacific(sent_log[rater_id]['resends'][-1]['utc'])}"
        elif rater_id in sent_log:
            mail = "send started, unconfirmed (rerun send to reconcile)"
        else:
            mail = "draft in Gmail, unsent" if rater_id in saved else "no draft"
        w = warmup.get(rater_id)
        warm = f"{w['numeric_ratings']}/{w['assigned_rows']}" if w else "none"
        role = "Author (coordinator)" if rater_id == "A1" else ROLE.get(people[rater_id]["group"], people[rater_id]["group"])
        csv_name = main_csv_entry(manifest, rater_id)["filename"]
        rows.append(f"| `{rater_id}` | {entry['rater_name']} | {people[rater_id]['email']} | {role} | {warm} | {mail} | "
                    f"**{done}/{len(table) - 1}** | [Sheet]({entry['sheet_url']}) · [CSV](ratings/{csv_name}) |")
    block = "\n".join([STATUS_START, f"Live progress read from the {len(index)} Sheets on {TODAY} at {__import__('time').strftime('%H:%M %Z')}; "
                       f"refresh with `python3 support/scripts/native_packet_generation/build_full_team_packets.py status`. "
                       f"Scored = rows with a `final_score_0_5` entry. Total scored: **{total}** of {100 * len(index)}.", "",
                       *([f"Team emails are on hold: {TEAM_SEND_HOLD}.", ""] if TEAM_SEND_HOLD else []),
                       "| ID | Rater | Email | Role | Warm-up | Packet email | Scored | Links |",
                       "| --- | --- | --- | --- | ---: | --- | ---: | --- |", *rows, STATUS_END])
    readme = EXPERIMENT / "README.md"
    text = readme.read_text()
    assert text.count(STATUS_START) == 1 and text.count(STATUS_END) == 1, "README needs one grading-status block"
    head, rest = text.split(STATUS_START)
    readme.write_text(head + block + rest.split(STATUS_END, 1)[1])
    print("\n".join(rows))
    print(f"total scored: {total}")


if __name__ == "__main__":
    {"plan": plan, "build": build, "sheets": sheets, "verify": verify, "drafts": drafts,
     "send-a1": send_a1, "send": send, "resend": resend, "export": export, "review": review, "status": status,
     "rationale-last": rationale_last}[sys.argv[1]]()
