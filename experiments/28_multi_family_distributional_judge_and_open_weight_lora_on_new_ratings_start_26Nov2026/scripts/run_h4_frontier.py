#!/usr/bin/env python3
"""Experiment 28: Run zero-demo distributional prompt (H4) across frontier CLI subscription lanes.

Supports:
  - codex_astra : GPT-6 Astra (high reasoning) via Codex CLI (`CODEX_HOME=~/.codex-vals`)
  - agy_argon   : Gemini 4 Argon (high) via Antigravity CLI (`agy`)
  - agy_opus    : Claude Opus 5.5 (high) via Antigravity CLI (`agy`)
  - grok_47     : Grok 4.7 (high reasoning) via Grok CLI (`grok`)

No paid API keys are set or used. Resumable by request id.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import tempfile
import threading
import time
from pathlib import Path

WRITE_LOCK = threading.Lock()


def parse_h4_json(raw: str) -> dict | None:
    i = raw.find("{")
    if i < 0:
        return None
    try:
        obj, _ = json.JSONDecoder().raw_decode(raw[i:])
        s = int(obj["final_score_0_5"])
        dist = obj["score_distribution"]
        probs = [float(dist[str(k)]) for k in range(6)]
        tot = sum(probs)
        if not (0 <= s <= 5) or any(p < 0 for p in probs) or abs(tot - 1.0) > 0.05:
            return None
        probs = [p / tot for p in probs]
        return {
            "final_score_0_5": s,
            "probs": probs,
            "expected_score": sum(k * p for k, p in enumerate(probs)),
            "A": str(obj.get("A", "")).strip(),
            "B": str(obj.get("B", "")).strip(),
            "C": str(obj.get("C", "")).strip(),
            "D": str(obj.get("D", "")).strip(),
            "base_score": int(obj["base_score"]) if obj.get("base_score") is not None else s,
            "confidence": str(obj.get("confidence", "")).strip(),
        }
    except Exception:
        return None


def base_clean_env() -> dict[str, str]:
    drop = {"ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY", "XAI_API_KEY"}
    return {k: v for k, v in os.environ.items() if k not in drop}


def call_lane(lane: str, system: str, user: str, timeout: int = 300) -> tuple[str, dict | None]:
    prompt = system + "\n\n" + user
    env = base_clean_env()
    with tempfile.TemporaryDirectory() as empty:
        if lane == "codex_astra":
            env["CODEX_HOME"] = str(Path.home() / ".codex-vals")
            cmd = [
                "codex", "--ask-for-approval", "never", "exec", "--json",
                "--skip-git-repo-check", "--sandbox", "read-only",
                "--model", "gpt-6-astra", "--ignore-user-config",
                "-c", "forced_login_method=chatgpt",
                "-c", 'model_reasoning_effort="high"', "-",
            ]
            r = subprocess.run(cmd, input=prompt, capture_output=True, text=True, cwd=empty, env=env, timeout=timeout)
            text, usage = "", None
            for line in r.stdout.splitlines():
                try:
                    ev = json.loads(line)
                except ValueError:
                    continue
                if ev.get("type") == "item.completed" and ev["item"].get("type") == "agent_message":
                    text = ev["item"].get("text", "")
                elif ev.get("type") == "turn.completed":
                    usage = ev.get("usage")
            if r.returncode != 0 or not text:
                raise RuntimeError(f"codex exit={r.returncode} stderr={r.stderr[-250:]}")
            return text, usage

        elif lane in ("agy_argon", "agy_opus"):
            model = "gemini-4-argon-high" if lane == "agy_argon" else "claude-opus-5-5-high"
            cmd = ["agy", "--dangerously-skip-permissions", "--model", model, f"-p={prompt}"]
            r = subprocess.run(cmd, input="", capture_output=True, text=True, cwd=empty, env=env, timeout=timeout)
            text = r.stdout.strip()
            if r.returncode != 0 or not text:
                raise RuntimeError(f"agy({model}) exit={r.returncode} stderr={r.stderr[-250:]}")
            return text, None

        elif lane == "grok_47":
            cmd = [
                "grok", "-p", "--model", "grok-4.7", "--effort", "high",
                "--tools", "", "--system-prompt-override", system, user,
            ]
            r = subprocess.run(cmd, input="", capture_output=True, text=True, cwd=empty, env=env, timeout=timeout)
            text = r.stdout.strip()
            if r.returncode != 0 or not text:
                raise RuntimeError(f"grok exit={r.returncode} stderr={r.stderr[-250:]}")
            return text, None

        else:
            raise ValueError(f"Unknown lane: {lane}")


def process_one(lane: str, row: dict, req_sha: str, out_path: Path, retries: int = 2) -> dict:
    t0 = time.time()
    last_err = ""
    for attempt in range(retries + 1):
        try:
            text, usage = call_lane(lane, row["system"], row["user"])
            parsed = parse_h4_json(text)
            if parsed is not None:
                rec = {
                    "id": row["id"],
                    "lane": lane,
                    "status": "ok",
                    "parsed": parsed,
                    "raw_response": text,
                    "usage": usage,
                    "elapsed_seconds": round(time.time() - t0, 2),
                    "requests_sha256": req_sha,
                    "attempt": attempt + 1,
                }
                with WRITE_LOCK:
                    with out_path.open("a", encoding="utf-8") as f:
                        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
                return rec
            last_err = f"unparsable JSON: {text[:180]}"
        except Exception as exc:  # noqa: BLE001
            last_err = str(exc)[:250]
        time.sleep(2.0 * (attempt + 1))

    rec = {
        "id": row["id"],
        "lane": lane,
        "status": "error",
        "error": last_err,
        "elapsed_seconds": round(time.time() - t0, 2),
        "requests_sha256": req_sha,
    }
    with WRITE_LOCK:
        with out_path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    return rec


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lane", required=True, choices=["codex_astra", "agy_argon", "agy_opus", "grok_47"])
    ap.add_argument("--requests", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--repeats", type=int, default=1)
    ap.add_argument("--only-ids", default="")
    args = ap.parse_args()

    req_path = Path(args.requests)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    req_sha = hashlib.sha256(req_path.read_bytes()).hexdigest()

    base_rows = [json.loads(l) for l in req_path.read_text().splitlines() if l.strip()]
    if args.only_ids:
        keep = set(args.only_ids.split(","))
        base_rows = [r for r in base_rows if r["id"] in keep]

    rows = []
    if args.repeats > 1:
        for rep in range(1, args.repeats + 1):
            for r in base_rows:
                rr = dict(r)
                rr["id"] = f"{r['id']}#r{rep}"
                rows.append(rr)
    else:
        rows = base_rows

    done = set()
    if out_path.exists():
        for l in out_path.read_text().splitlines():
            if not l.strip():
                continue
            o = json.loads(l)
            if o.get("status") == "ok":
                done.add(o["id"])

    todo = [r for r in rows if r["id"] not in done]
    print(f"[{args.lane}] total={len(rows)} done={len(done)} todo={len(todo)} workers={args.workers}", flush=True)
    if not todo:
        return

    ok_cnt, err_cnt = 0, 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(process_one, args.lane, r, req_sha, out_path) for r in todo]
        for i, fut in enumerate(concurrent.futures.as_completed(futs), 1):
            rec = fut.result()
            if rec["status"] == "ok":
                ok_cnt += 1
                s = rec["parsed"]["final_score_0_5"]
                e = rec["parsed"]["expected_score"]
                if i <= 5 or i % 15 == 0 or i == len(todo):
                    print(f"[{args.lane}] {i}/{len(todo)} id={rec['id']} score={s} E={e:.2f} ({rec['elapsed_seconds']}s)", flush=True)
            else:
                err_cnt += 1
                print(f"[{args.lane}] ERROR {i}/{len(todo)} id={rec['id']}: {rec.get('error')}", flush=True)
    print(f"[{args.lane}] FINISHED: ok={ok_cnt} err={err_cnt}", flush=True)


if __name__ == "__main__":
    main()
