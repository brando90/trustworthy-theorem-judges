"""Plan, build and verify the full-team 75-file rating packets (one per rater).

    plan    write the private roster/design and one Sheet request file per rater
    build   build every rater's packet and unsent email text (needs created Sheet IDs)
    verify  bind each build to the digest of its live Sheet table
    drafts  save the unsent emails to the Gmail Drafts folder (nothing is sent)

Row order per rater: files stay grouped by task; the starting task rotates and the
task/file direction alternates across raters, so partial top-down work still covers
all tasks evenly and no agent is always rated first. Order never uses file content.
"""

from __future__ import annotations

import csv
import hashlib
import io
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import build_packet as bp  # noqa: E402

REPO = HERE.parents[4]
OUT = REPO / "research_artifacts/09_human_rating_collection/preparation_11-09-2026/full_team_11-14-2026"
SEALED = OUT / "sealed"
COHORT = SEALED / "RATABLE_COHORT_75_V2.json"
TEMPLATE_SHEET_ID = "1Hpcb4NP754RDWstDkiaTR59K9AX2vXNL6IR9iXKRo-Y"
TEMPLATE_TAB_ID = 0
BRANDO_SHEET_ID = "1zUDr9fpUwK0IuxrSdFfBR_mOt4WwMY8-doBC6cIhIHM"
SUBJECT = "VeriBench human-rating main rating task: closes Thursday, 11-19-2026, 6pm PT"
BCC = ["brando.science@gmail.com", "brandojazz@gmail.com", "brando9@stanford.edu"]
PUBLIC_START = ("https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/"
                "09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/"
                "main_rating_task/START_HERE.md")
COAUTHOR = ("Would you be willing to help with a human-rating task for VeriBench? Your ratings would be really "
            "valuable, and if you are interested and have time, I would be happy to add you as a co-author on "
            "the papers this data is used for. No pressure at all.")
OPENERS = {
    "coauthor": COAUTHOR,
    "varun": COAUTHOR + " Doing these ratings is also a great way to get intimately familiar with Lean 4 "
             "autoformalization\u2014and if you have seen Andrej Karpathy's and Rylan Schaeffer's advice on "
             "becoming a top machine learning researcher (for example, how much of ImageNet Karpathy inspected "
             "firsthand), looking closely at the actual data yourself is essential.",
    "weekend": "Your ratings would be extremely valuable. If you can finish over the weekend, that would be even "
               "better, as many ratings as you have time for.",
}
# rater_id, verified name, greeting, delivery email, group, opener (aligned with RATER_IDENTITIES.json & ROSTER.csv)
PEOPLE = [
    ("T01", "Rylan Schaeffer", "Rylan", "rschaef@cs.stanford.edu", "author", ""),
    ("T02", "Yegor Denisov-Blanch", "Yegor", "ydebl@stanford.edu", "author (extra-only designation preserved)", ""),
    ("T03", "Dilara Soylu", "Dilara", "soylu@stanford.edu", "author", ""),
    ("T04", "Allen Nie", "Allen", "aimingnie@gmail.com", "author", ""),
    ("T05", "Srivatsava Daruru (Sri)", "Srivatsava", "vatsava@gmail.com", "author", ""),
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


def ordered_items(spec: dict) -> list[str]:
    """Same result as the Sheet requests: sort by task then file, then rotate whole tasks."""
    rows = sorted(cohort_rows(), key=lambda r: r[2], reverse=spec["file_descending"])
    rows = sorted(rows, key=lambda r: r[1], reverse=spec["task_descending"])  # stable: keeps file order
    cut = 3 * spec["start_task_offset"]
    return [r[0] for r in rows[cut:] + rows[:cut]]


def sheet_requests(name: str, rater_id: str, spec: dict) -> list[dict]:
    column = lambda c: {"sheetId": TEMPLATE_TAB_ID, "startRowIndex": 1, "endRowIndex": 76,
                        "startColumnIndex": c, "endColumnIndex": c + 1}
    order = lambda descending: "DESCENDING" if descending else "ASCENDING"
    requests = [
        {"findReplace": {"find": "Brando Miranda", "replacement": name, "range": column(0),
                         "matchCase": True, "matchEntireCell": True}},
        {"findReplace": {"find": "A1", "replacement": rater_id, "range": column(1),
                         "matchCase": True, "matchEntireCell": True}},
        {"sortRange": {"range": {"sheetId": TEMPLATE_TAB_ID, "startRowIndex": 1, "endRowIndex": 76,
                                 "startColumnIndex": 0, "endColumnIndex": 11},
                       "sortSpecs": [{"dimensionIndex": 3, "sortOrder": order(spec["task_descending"])},
                                     {"dimensionIndex": 4, "sortOrder": order(spec["file_descending"])}]}},
    ]
    if spec["start_task_offset"]:
        requests.append({"moveDimension": {"source": {"sheetId": TEMPLATE_TAB_ID, "dimension": "ROWS",
                                                      "startIndex": 1, "endIndex": 1 + 3 * spec["start_task_offset"]},
                                           "destinationIndex": 76}})
    return requests


def roster() -> list[dict]:
    people = []
    for index, (rater_id, name, greeting, email, group, opener) in enumerate(PEOPLE, 1):
        people.append({"rater_id": rater_id, "rater_name": name, "greeting": greeting, "email": email,
                       "group": group, "opener": opener, "design": design(index),
                       "sheet_title": f"VeriBench main rating sheet — {name} — 75 files"})
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


def email_body(person: dict, sheet_url: str) -> str:
    opener = OPENERS[person["opener"]] + "\n\n" if person["opener"] else ""
    return f"""Hi {person['greeting']},

{opener}Your VeriBench rating packet is attached: 75 agent files in 25 task folders. Your sheet lists them in your own order; please work from the top down and do as many as you can, even a few helps.

Your personal rating sheet:
{sheet_url}

What to do:
1. Unzip the attachment and read START_HERE.md.
2. In each task folder, compare the agent's theorem statements in agent_lean/ with the reference statements in gold_lean/, and rate how well the agent's statements cover the reference (not the proofs).
3. In your sheet, for each file enter a score from 0 to 5 and a one-sentence rationale in your own words, and answer yes, no or unsure to the AI question (column ai_assisted_rating_attestation). This is a first round, so I would love your feedback on the form: if the rationale is too much work, or you would prefer not to have that column, please tell me. If anything in a task looks wrong, just email me.

Please choose the score yourself and use AI only for help with Lean notation or a specific point. Your sheet saves automatically, so there is nothing to send back.

Please finish by 6pm Pacific on Thursday, 11-19-2026 if you can, so I can run experiments overnight and show results in a meeting the next day. If you can only get part of it done by then, that is still very helpful. Filling it in as you go is even better: your sheet saves automatically, and I will pull the data and start my analysis as it comes in, so we can iterate.

P.S. Feel free to email me with any questions. Email is preferred for questions! Happy to clarify anything! The full instructions are also public at {PUBLIC_START}

Brando (drafted with Antigravity)
-----
Brando Miranda
Ph.D. Student
Computer Science, Stanford University
EDGE Scholar, Stanford University
brando9@stanford.edu
website: https://brando90.github.io/brandomiranda/
"""


def build() -> None:
    created = json.loads((SEALED / "SHEETS_CREATED.json").read_text())
    index = {}
    builds = SEALED / "builds"
    people = roster()
    brando = {"rater_id": "A1", "rater_name": "Brando Miranda", "design":
              {"task_descending": False, "file_descending": False, "start_task_offset": 0}}
    for person in [brando] + people:
        rater_id = person["rater_id"]
        sheet_id = BRANDO_SHEET_ID if rater_id == "A1" else created[rater_id]
        url = f"https://docs.google.com/spreadsheets/d/{sheet_id}/edit"
        out = builds / rater_id
        if not out.exists():
            bp.build_packet(COHORT, out, rater_name=person["rater_name"], rater_id=rater_id, sheet_url=url,
                            row_order=ordered_items(person["design"]))
        receipt = json.loads((out / "ASSEMBLY_RECEIPT.json").read_text())
        assert receipt["sheet_url"] == url and receipt["artifact_count"] == 75 and receipt["task_count"] == 25
        table = list(csv.reader(io.StringIO((out / "rating_task_packet/ratings.csv").read_text())))
        index[rater_id] = {"rater_name": person["rater_name"], "sheet_id": sheet_id, "sheet_url": url,
                           "expected_table_digest": bp.table_digest(table), "zip": receipt["archive_path"],
                           "zip_sha256": receipt["archive_sha256"], "status": receipt["status"]}
        if rater_id != "A1":
            (SEALED / "drafts").mkdir(exist_ok=True)
            draft = {"to": person["email"], "bcc": BCC, "subject": SUBJECT, "body": email_body(person, url),
                     "attachment": receipt["archive_path"], "attachment_sha256": receipt["archive_sha256"]}
            (SEALED / "drafts" / f"{rater_id}.json").write_text(json.dumps(draft, indent=1, ensure_ascii=False) + "\n")
    (SEALED / "BUILD_INDEX.json").write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps({r: [v["sheet_id"], v["expected_table_digest"]] for r, v in index.items()}))


def verify() -> None:
    """Input: sealed/LIVE_DIGESTS.json {sheet_id: 'digest:rows:rows_with_responses'} read in the owner's browser."""
    observed = json.loads((SEALED / "LIVE_DIGESTS.json").read_text())
    index = json.loads((SEALED / "BUILD_INDEX.json").read_text())
    bad = []
    for rater_id, entry in index.items():
        digest, rows, responses = observed.get(entry["sheet_id"], "::").split(":")
        try:
            assert responses == "0", "live Sheet already has responses"
            bp.verify_sheet_digest(SEALED / "builds" / rater_id, digest, int(rows or 0),
                                   "gviz CSV read of Ratings!A1:K76 in the owner's signed-in browser, 11-14-2026")
            entry["status"] = "BUILT_SHEET_MATCHED_NOT_SENT"
        except (AssertionError, ValueError) as error:
            bad.append((rater_id, str(error)))
            entry["status"] = "HELD"
    (SEALED / "BUILD_INDEX.json").write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n")
    print(f"matched {len(index) - len(bad)} of {len(index)}; held: {bad}")


def drafts() -> None:
    import imaplib
    import time
    from email.message import EmailMessage
    password = (Path.home() / "keys/gmail_app_password.txt").read_text().strip()
    index = json.loads((SEALED / "BUILD_INDEX.json").read_text())
    log_path = SEALED / "DRAFTS_SAVED.json"
    saved = json.loads(log_path.read_text()) if log_path.exists() else {}
    with imaplib.IMAP4_SSL("imap.gmail.com") as box:
        box.login("brandojazz@gmail.com", password)
        for path in sorted((SEALED / "drafts").glob("*.json")):
            rater_id = path.stem
            if rater_id in saved:
                continue
            assert index[rater_id]["status"] == "BUILT_SHEET_MATCHED_NOT_SENT", rater_id
            draft = json.loads(path.read_text())
            data = Path(draft["attachment"]).read_bytes()
            assert sha(data) == draft["attachment_sha256"]
            message = EmailMessage()
            message["From"] = "Brando Miranda <brandojazz@gmail.com>"
            message["To"], message["Bcc"], message["Subject"] = draft["to"], ", ".join(draft["bcc"]), draft["subject"]
            message.set_content(draft["body"])
            message.add_attachment(data, maintype="application", subtype="zip", filename=Path(draft["attachment"]).name)
            status, reply = box.append("[Gmail]/Drafts", "\\Draft", imaplib.Time2Internaldate(time.time()), message.as_bytes())
            assert status == "OK", reply
            saved[rater_id] = {"to": draft["to"], "append_reply": reply[0].decode(errors="replace"), "sent": False}
            log_path.write_text(json.dumps(saved, indent=1) + "\n")
    print(f"{len(saved)} unsent drafts are in Gmail Drafts; nothing was sent")


if __name__ == "__main__":
    {"plan": plan, "build": build, "verify": verify, "drafts": drafts}[sys.argv[1]]()
