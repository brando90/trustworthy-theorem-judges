# TLDR: Refuse packet delivery and rater qualification when the current packet has unresolved reference defects or an unverified release record.
import hashlib
import json
from pathlib import Path

EXP = Path(__file__).resolve().parents[1]
STATUS = EXP / "human_round/PACKET_STATUS.json"
PACKETS = {"warmup": EXP / "human_round/warmup/packet", "setN": EXP / "human_round/sample_setN/packet"}


def require_release(packet, status_path=STATUS):
    state = json.loads(Path(status_path).read_text())["packets"][packet]
    if state.get("status") != "RELEASED":
        raise SystemExit(f"{packet}: HOLD — {state['reason']} See human_round/PACKET_STATUS.json.")
    listing = PACKETS[packet] / "FILES.sha256"
    if hashlib.sha256(listing.read_bytes()).hexdigest() != state.get("files_sha256_digest"):
        raise SystemExit(f"{packet}: release digest does not match packet; audit the changed version first")
    if not state.get("acceptance_record"):
        raise SystemExit(f"{packet}: no reference acceptance record")
    acceptance = Path(status_path).resolve().parent / state["acceptance_record"]
    if not acceptance.is_file() or hashlib.sha256(acceptance.read_bytes()).hexdigest() != state.get("acceptance_record_sha256"):
        raise SystemExit(f"{packet}: reference acceptance record is missing or changed")
    for line in listing.read_text().splitlines():
        digest, rel = line.split(maxsplit=1)
        path = PACKETS[packet] / rel.lstrip("*")
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit(f"{packet}: source changed after release: {rel}")
