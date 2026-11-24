#!/usr/bin/env python3
"""Experiment 27: run the frozen H3 requests one after another on the Vals Codex plan (GPT-6 Astra, reasoning high, Codex CLI one-turn, read-only, no tools).

Dated 11-24-2026. Model calls. Each call goes through ~/.local/bin/vals-codex (account and included-usage reserve check, real-request sign-in check, profile lock),
so calls are serial. Resumable: ids already in the output file with status ok are skipped. The profile lock is shared with the plan router, so a failed call is retried up to 12 times 20 s apart; stops after 3 items fail in a row.
Run: python3 run_h3_vals_codex.py requests.jsonl out.jsonl [--only-split train,val]
"""
import argparse, hashlib, json, os, subprocess, sys, tempfile, time
from pathlib import Path

WRAP = str(Path.home() / ".local/bin/vals-codex")


def call(system, user, timeout=420):
    cmd = ["python3", WRAP, "--", "codex", "--ask-for-approval", "never", "exec", "--json", "--skip-git-repo-check", "--sandbox", "read-only",
           "--model", "gpt-6-astra", "--ignore-user-config", "-c", "forced_login_method=chatgpt", "-c", 'model_reasoning_effort="high"', "-"]
    env = {k: os.environ[k] for k in ("PATH", "HOME", "LANG", "USER") if k in os.environ}
    with tempfile.TemporaryDirectory() as empty:
        r = subprocess.run(cmd, input=system + "\n\n" + user, capture_output=True, text=True, cwd=empty, env=env, timeout=timeout)
    text, usage, tools = "", None, 0
    for line in r.stdout.splitlines():
        try:
            ev = json.loads(line)
        except ValueError:
            continue
        if ev.get("type") == "item.completed":
            it = ev["item"]
            if it.get("type") == "agent_message":
                text = it.get("text", "")
            elif it.get("type") != "reasoning":
                tools += 1
        if ev.get("type") == "turn.completed":
            usage = ev.get("usage")
    if r.returncode or not text:
        raise RuntimeError(f"vals-codex exit {r.returncode}: {r.stderr[-200:]}")
    if tools:
        raise RuntimeError("unexpected tool item")
    return text, usage


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("requests"); ap.add_argument("out"); ap.add_argument("--only-split", default="")
    a = ap.parse_args()
    rows = [json.loads(l) for l in open(a.requests)]
    if a.only_split:
        rows = [r for r in rows if r["split"] in a.only_split.split(",")]
    sha = hashlib.sha256(open(a.requests, "rb").read()).hexdigest()
    done = set()
    if os.path.exists(a.out):
        done = {json.loads(l)["id"] for l in open(a.out) if json.loads(l)["status"] == "ok"}
    todo = [r for r in rows if r["id"] not in done]
    print(f"{len(done)} done, {len(todo)} to run", flush=True)
    fails = 0
    for r in todo:
        t0 = time.time()
        try:
            for attempt in range(12):  # the profile lock is shared with the plan router: wait and retry on a busy or blocked answer
                try:
                    text, usage = call(r["system"], r["user"])
                    break
                except RuntimeError as e:
                    if attempt == 11:
                        raise
                    time.sleep(20)
            rec = {"id": r["id"], "split": r["split"], "model": "gpt-6-astra", "route": "vals-codex", "status": "ok", "raw_response": text, "usage": usage,
                   "elapsed_seconds": round(time.time() - t0, 2), "requests_sha256": sha}
            fails = 0
        except Exception as e:  # noqa: BLE001
            rec = {"id": r["id"], "split": r["split"], "status": "error", "error": str(e)[:300], "requests_sha256": sha}
            fails += 1
        with open(a.out, "a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(r["id"], rec["status"], rec.get("elapsed_seconds"), flush=True)
        if fails >= 3:
            print("3 failures in a row: stop", flush=True); sys.exit(2)


if __name__ == "__main__":
    main()
