# TLDR: Amendment C15 item 5's folder assignment for rating set N: gives each of the 25 task folders two distinct qualified raters within each rater's pledge, pairing one team and one vendor rater per folder while both groups have capacity, and keeps already-delivered folders fixed (--keep); seeded (20261009), zero model calls, uses folder ids only (no system information).
"""Usage from the trustworthy-theorem-judges root (supply the current private roster and delivered assignments):
  python3 experiments/09_human_rating_collection/support/scripts/legacy/assign_setN_folders.py --roster research_artifacts/ROSTER.csv \
      [--include-pending] [--keep research_artifacts/DELIVERED.csv] [--out research_artifacts/ASSIGNMENT.csv]

ROSTER.csv columns: rater_id, pool (team|vendor), pledged_folders (int), qualified (yes|no|pending), name (optional).
A1 is never assigned (A1 rates every folder as a sensitivity rater, C8 item 3).
Without --include-pending only qualified raters get folders; with it, pending raters are planned provisionally
(for Friday's plan before warm-ups are scored) and marked as such.
--keep takes an assignment CSV (task_folder, slot, rater_id) of folders already delivered; those rows are pinned
before anything else is planned, so a re-plan after the roster changes never moves a delivered folder.
Prints a Markdown summary; writes the assignment CSV (keep it in the git-ignored private_ratings_setN/).
"""
import argparse
import csv
from pathlib import Path

import numpy as np

# Use the pinned committed snapshot, not the stale shared VeriBench checkout.
EXP = (Path(__file__).resolve().parents[5] / "research_artifacts/09_human_rating_collection/upstream_source"
       / "experiments/102_rescore_vbv1_paper_fsc_with_validated_judge_rewrite_tmlr_icml")
PACKET = EXP / "human_round/sample_setN/packet"
SEED = 20261009
PER_FOLDER = 2


def load_roster(path, include_pending):
    raters = []
    for r in csv.DictReader(line for line in open(path) if not line.startswith("#")):
        rid = r["rater_id"].strip()
        status = r["qualified"].strip().lower()
        if rid == "A1" or status == "no" or (status == "pending" and not include_pending):
            continue
        raters.append({"id": rid, "pool": r["pool"].strip().lower(), "pledge": int(r["pledged_folders"]),
                       "status": status, "left": int(r["pledged_folders"])})
    return raters


def pick(cands, rng):
    """Most remaining capacity relative to pledge first; seeded random tie-break."""
    if not cands:
        return None
    keys = [(-(c["left"] / c["pledge"]), rng.random()) for c in cands]
    return cands[min(range(len(cands)), key=lambda i: keys[i])]


def load_keep(path, raters):
    """Delivered (task_folder, rater_id) pairs to pin; every pinned rater must be an eligible rater in the roster."""
    ids = {r["id"] for r in raters}
    pinned = {}
    for r in csv.DictReader(line for line in open(path) if not line.startswith("#")):
        rid, f = r["rater_id"].strip(), r["task_folder"].strip()
        if rid not in ids:
            raise SystemExit(f"--keep: rater {rid} (folder {f}) is not an eligible rater in the roster; fix the roster first")
        pinned.setdefault(f, []).append(rid)
    return pinned


def assign(folders, raters, seed=SEED, pinned=None):
    """Pass 1 gives every folder one rater before any folder gets a second (more tasks beat a second rating when
    capacity is short; C15 simulation). Pass 2 adds a second rater, preferring the other group, so folders get one team
    and one vendor rater while both groups have capacity. A rater never gets the same folder twice. Pinned
    (already delivered) folders are filled first and never changed."""
    rng = np.random.default_rng(seed)
    order = [folders[i] for i in rng.permutation(len(folders))]
    plan = {f: [] for f in folders}
    pool_of = {r["id"]: r["pool"] for r in raters}
    for f, rids in (pinned or {}).items():
        if f not in plan:
            raise SystemExit(f"--keep: unknown folder {f}")
        for rid in rids:
            r = next(x for x in raters if x["id"] == rid)
            if rid in plan[f] or r["left"] <= 0 or len(plan[f]) >= PER_FOLDER:
                raise SystemExit(f"--keep: cannot pin {rid} to {f} (duplicate, pledge exhausted or folder full)")
            plan[f].append(rid); r["left"] -= 1
    for slot in range(PER_FOLDER):
        for f in order:
            if len(plan[f]) > slot:
                continue
            free = [r for r in raters if r["left"] > 0 and r["id"] not in plan[f]]
            if plan[f]:
                other = [r for r in free if r["pool"] != pool_of[plan[f][0]]]
                free = other or free
            r = pick(free, rng)
            if r is None:
                continue
            plan[f].append(r["id"]); r["left"] -= 1
    return plan


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--roster", required=True)
    ap.add_argument("--include-pending", action="store_true")
    ap.add_argument("--keep", default="", help="assignment CSV of already-delivered folders to pin (task_folder, slot, rater_id)")
    ap.add_argument("--out", default=str(EXP / "human_round/private_ratings_setN/ASSIGNMENT.csv"))
    ap.add_argument("--folders", type=int, default=0, help="number of folders (default: count N* folders in the final packet)")
    a = ap.parse_args()
    n = a.folders or len([p for p in PACKET.glob("N[0-9][0-9]") if p.is_dir()])
    folders = [f"N{i:02d}" for i in range(1, n + 1)]
    raters = load_roster(a.roster, a.include_pending)
    pinned = load_keep(a.keep, raters) if a.keep else {}
    plan = assign(folders, raters, pinned=pinned)
    status = {r["id"]: r["status"] for r in raters}
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["task_folder", "slot", "rater_id", "provisional"])
        for fo in folders:
            for k, rid in enumerate(plan[fo], start=1):
                w.writerow([fo, k, rid, "yes" if status[rid] == "pending" else "no"])
    need = PER_FOLDER * len(folders)
    filled = sum(len(v) for v in plan.values())
    mixed = sum(1 for v in plan.values() if len({next(r["pool"] for r in raters if r["id"] == x) for x in v}) == 2)
    print(f"## Set N folder assignment (seed {SEED}){' — PROVISIONAL (includes pending raters)' if a.include_pending else ''}\n")
    print(f"- Slots filled: {filled}/{need} ({PER_FOLDER} per folder x {len(folders)} folders); unfilled: {need - filled}")
    print(f"- Folders with one team + one vendor rater: {mixed}/{len(folders)}")
    print(f"- Capacity offered: {sum(r['pledge'] for r in raters)} folder ratings from {len(raters)} raters")
    print(f"- Pinned (already delivered, --keep): {sum(len(v) for v in pinned.values())} slots in {len(pinned)} folders\n")
    print("| Rater | Group | Pledge | Assigned | Folders |\n|---|---|---:|---:|---|")
    for r in sorted(raters, key=lambda r: r["id"]):
        mine = [fo for fo in folders if r["id"] in plan[fo]]
        print(f"| {r['id']}{' (pending)' if r['status'] == 'pending' else ''} | {r['pool']} | {r['pledge']} | {len(mine)} | {', '.join(mine)} |")
    for k in range(PER_FOLDER):
        short = [fo for fo in folders if len(plan[fo]) == k]
        if short:
            print(f"\nFolders with {k} rater(s): {', '.join(short)}")
    print(f"\nWrote {a.out}")


if __name__ == "__main__":
    main()
