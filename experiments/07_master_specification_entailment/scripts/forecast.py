#!/usr/bin/env python3
"""Bounded, append-only local forecasts; a reserved call is never retried."""
import argparse
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(obj):
    return (json.dumps(obj, sort_keys=True, ensure_ascii=False, allow_nan=False) + "\n").encode()


def read_json(path):
    return json.loads(Path(path).read_text())


def atomic_json(path, obj):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_bytes(encoded(obj))
    os.replace(temp, path)


def rows(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def parse_prediction(content):
    """No regex extraction, prose fallback, bool-as-number, NaN, or clipping."""
    def reject_constant(value):
        raise ValueError("Nonfinite JSON constant")
    def unique_pairs(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("Duplicate JSON key")
            result[key] = value
        return result
    value = json.loads(content, parse_constant=reject_constant, object_pairs_hook=unique_pairs)
    if not isinstance(value, dict) or set(value) != {"status", "probability", "reason"}:
        raise ValueError("Expected exact response keys")
    if not isinstance(value["reason"], str):
        raise ValueError("Reason must be a string")
    p = value["probability"]
    if value["status"] == "abstain" and p is None:
        return {"status": "abstain", "probability": None}
    if value["status"] != "forecast" or type(p) not in (int, float) or not math.isfinite(p) or not 0 <= p <= 1:
        raise ValueError("Invalid probability/status")
    return {"status": "forecast", "probability": float(p)}


def verify_freeze():
    frozen = read_json(ROOT / "inference_freeze.json")
    for name, digest in frozen["files"].items():
        if sha((ROOT / name).read_bytes()) != digest:
            raise RuntimeError("Changed fixed input: " + name)
    return frozen


def load_inputs():
    inputs = rows(ROOT / "inputs.jsonl")
    labels = read_json(ROOT / "labels.json")
    if isinstance(labels, dict):
        labels = labels["items"]
    assert len(inputs) == len(labels) <= 48
    assert all(set(row) == {"id", "statement"} for row in inputs)
    assert len({row["id"] for row in inputs}) == len(inputs)
    assert {row["id"] for row in inputs} == {row["id"] for row in labels}
    return {row["id"]: row for row in inputs}, labels


def freeze(model_file):
    if (ROOT / "inference_freeze.json").exists():
        verify_freeze()
        print("Existing inference freeze verified; budgets unchanged.")
        return
    model = read_json(model_file)
    atomic_json(ROOT / "model_identity.json", model)
    inputs, labels = load_inputs()
    split_families = {}
    for split in ("train", "validation", "test"):
        split_families[split] = sorted({r["family"] for r in labels if r["split"] == split})
        assert len(split_families[split]) == 2
    assert len(set(sum(split_families.values(), []))) == 6
    # Hash all existing construction/certificate sources and receipts as well as the harness.
    names = [p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
             if p.is_file() and p.suffix in {".py", ".lean", ".json", ".jsonl", ".md"}
             and "__pycache__" not in p.parts and "results" not in p.relative_to(ROOT).parts
             and not p.name.startswith("CKPT") and p.name not in {"README.md", "results.md", "inference_freeze.json"}]
    construction_receipt = read_json(ROOT / "results/certificate_validation.json")
    assert construction_receipt["all_construction_predictions_verified"] is True
    assert construction_receipt["input_sha256"] == sha((ROOT / "inputs.jsonl").read_bytes())
    names += ["results/certificate_validation.json", "results/checker_tests.json", "lean/lean-toolchain"]
    result = {"created_unix": time.time(), "files": {n: sha((ROOT / n).read_bytes()) for n in sorted(names)},
              "n_primary": len(inputs), "split_families": split_families,
              "scientific_budgets": {"primary_calls": len(inputs), "preflight_calls": 1,
                  "transport_diagnostics": 2, "max_output_tokens": 2048, "call_timeout_seconds": 120,
                  "clients": 1, "retry_policy": "never retry a reserved call", "provider_cost_usd": 0}}
    atomic_json(ROOT / "inference_freeze.json", result)
    print(json.dumps({"freeze_sha256": sha((ROOT / "inference_freeze.json").read_bytes()), "primary": len(inputs)}))


def get_payload(statement, preflight=False):
    model = read_json(ROOT / "model_identity.json")
    if preflight:
        system = "Return exactly the requested JSON object, without extra text."
        user = 'Label-reproduction transport check. Return exactly {"status":"forecast","probability":0.375,"reason":"label reproduction"}'
    else:
        system = (ROOT / "prompts/judge.md").read_text()
        user = "Statements to judge:\n\n" + statement
    payload = {"model": model["served_model_id"], "messages": [{"role": "system", "content": system}, {"role": "user", "content": user}],
               "temperature": 0.0, "top_p": 1.0, "max_tokens": 2048, "seed": 20261108,
               "stream": False, "chat_template_kwargs": {"enable_thinking": False}}
    return payload


def call_once(runtime, url, call_id, statement, kind, deadline):
    """Holding the process lock ensures one client; reservation makes crash recovery conservative."""
    out = runtime / "calls" / call_id
    out.mkdir(parents=True, exist_ok=True)
    receipt_path = out / "receipt.json"
    reservation = out / "reservation.json"
    if receipt_path.exists():
        return read_json(receipt_path)
    if reservation.exists():
        r = read_json(reservation)
        r.update(status="interrupted_reserved_call", probability=None)
        atomic_json(receipt_path, r)
        return r
    if time.time() + 125 > deadline:
        raise RuntimeError("Not enough original run budget to admit a call")
    payload = get_payload(statement, preflight=kind == "preflight")
    request = encoded(payload)
    receipt = {"id": call_id, "kind": kind, "started_unix": time.time(),
               "request_sha256": sha(request), "input_sha256": sha(statement.encode()),
               "inference_freeze_sha256": sha((ROOT / "inference_freeze.json").read_bytes()),
               "provider_cost_usd": 0, "status": "reserved", "probability": None}
    # Exclusive creation is an additional fence against an accidental second writer.
    with reservation.open("xb") as stream:
        stream.write(encoded(receipt))
        stream.flush()
        os.fsync(stream.fileno())
    (out / "request.json").write_bytes(request)
    started = time.monotonic()
    try:
        req = urllib.request.Request(url.rstrip("/") + "/chat/completions", request, {"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=120) as response:
            raw = response.read(2_000_000)
        (out / "response.json").write_bytes(raw)
        receipt["response_sha256"] = sha(raw)
        response = json.loads(raw)
        receipt["actual_model"] = response.get("model")
        receipt["usage"] = response.get("usage", {})
        choice = response["choices"][0]
        receipt["finish_reason"] = choice.get("finish_reason")
        content = choice["message"].get("content")
        receipt["content_sha256"] = sha((content or "").encode())
        if receipt["finish_reason"] != "stop":
            raise ValueError("Incomplete model answer")
        if receipt["actual_model"] != payload["model"]:
            raise ValueError("Unexpected served model identity")
        if receipt["usage"].get("completion_tokens", 2049) > 2048:
            raise ValueError("Completion token cap exceeded")
        receipt.update(parse_prediction(content))
    except (urllib.error.URLError, TimeoutError, OSError) as error:
        receipt.update(status="transport_failure", error_type=type(error).__name__)
    except (ValueError, KeyError, IndexError, TypeError) as error:
        receipt.update(status="invalid_response", error_type=type(error).__name__)
    receipt["elapsed_seconds"] = time.monotonic() - started
    receipt["finished_unix"] = time.time()
    atomic_json(receipt_path, receipt)
    return receipt


def collect(runtime):
    return [read_json(p) for p in sorted((runtime / "calls").glob("*/receipt.json"))]


def publish(runtime):
    receipts = collect(runtime)
    atomic_json(ROOT / "results/forecasts.json", {"receipts": receipts})
    atomic_json(ROOT / "results/call_accounting.json", {
        "primary_reserved": len(list((runtime / "calls").glob("*/reservation.json"))) - sum(r["kind"] != "primary" for r in receipts),
        "primary_completed": sum(r["kind"] == "primary" for r in receipts),
        "preflight_calls": sum(r["kind"] == "preflight" for r in receipts),
        "transport_diagnostics": 0,
        "provider_cost_usd": 0,
        "completion_tokens": sum(r.get("usage", {}).get("completion_tokens", 0) for r in receipts),
        "prompt_tokens": sum(r.get("usage", {}).get("prompt_tokens", 0) for r in receipts)})


def run(args):
    verify_freeze()
    protocol = read_json(ROOT / "forecast_protocol.json")
    assert args.deadline <= protocol["primary_completion_deadline_unix"], "Original deadline cannot be reset"
    assert args.url.startswith("http://127.0.0.1:"), "This condition permits only the dedicated local free server"
    runtime = Path(args.runtime)
    runtime.mkdir(parents=True, exist_ok=True)
    with (runtime / "client.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        inputs, labels = load_inputs()
        if args.stage == "preflight":
            result = call_once(runtime, args.url, "preflight", "label-reproduction-0.375", "preflight", args.deadline)
            publish(runtime)
            assert result["status"] == "forecast" and result["probability"] == 0.375, "Preflight failed; no primary calls authorized by this harness"
            print(json.dumps(result))
            return
        preflight = read_json(runtime / "calls/preflight/receipt.json")
        assert preflight["status"] == "forecast" and preflight["probability"] == 0.375
        wanted = {"train", "validation"} if args.stage == "train_validation" else {"test"}
        if args.stage == "test":
            selection = read_json(ROOT / "results/selection.json")
            assert selection["inference_freeze_sha256"] == sha((ROOT / "inference_freeze.json").read_bytes())
            current = {r["id"]: r for r in collect(runtime)}
            prior = [current[r["id"]] for r in labels if r["split"] in {"train", "validation"}]
            assert selection["training_validation_receipts_sha256"] == sha(encoded(prior))
        for label in labels:
            if label["split"] in wanted:
                r = call_once(runtime, args.url, label["id"], inputs[label["id"]]["statement"], "primary", args.deadline)
                publish(runtime)
                print(json.dumps({k: r.get(k) for k in ("id", "status", "elapsed_seconds")}), flush=True)


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="command", required=True)
    f = sub.add_parser("freeze"); f.add_argument("--model-config", required=True)
    r = sub.add_parser("run")
    r.add_argument("--runtime", required=True); r.add_argument("--url", required=True)
    r.add_argument("--deadline", type=float, required=True)
    r.add_argument("--stage", choices=["preflight", "train_validation", "test"], required=True)
    a = p.parse_args()
    freeze(a.model_config) if a.command == "freeze" else run(a)


if __name__ == "__main__":
    main()
