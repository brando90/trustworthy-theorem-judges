#!/usr/bin/env python3
"""Independent arithmetic and optional byte-level verification of saved forecasts."""
import argparse
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads(path.read_text())


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--runtime", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    labels = read(ROOT / "labels.json")
    inputs = {r["id"]: r for r in map(json.loads, (ROOT / "inputs.jsonl").read_text().splitlines())}
    receipts = read(ROOT / "results/forecasts.json")["receipts"]
    primary = {r["id"]: r for r in receipts if r["kind"] == "primary"}
    assert len(receipts) == 49 and len(primary) == 48
    assert set(primary) == {r["id"] for r in labels}
    freeze = read(ROOT / "inference_freeze.json")
    for name, expected in freeze["files"].items():
        assert digest((ROOT / name).read_bytes()) == expected, name
    selection = read(ROOT / "results/selection.json")
    prior = [primary[r["id"]] for r in labels if r["split"] in {"train", "validation"}]
    encoded = (json.dumps(prior, sort_keys=True, ensure_ascii=False, allow_nan=False) + "\n").encode()
    assert digest(encoded) == selection["training_validation_receipts_sha256"]
    for label in labels:
        r = primary[label["id"]]
        assert r["started_unix"] >= freeze["created_unix"]
        assert r["elapsed_seconds"] <= 120.5
        assert r.get("usage", {}).get("completion_tokens", 0) <= 2048
        assert r["input_sha256"] == digest(inputs[label["id"]]["statement"].encode())
        if label["split"] == "test":
            assert r["started_unix"] > selection["selected_unix"]
    trace = None
    if args.runtime:
        for r in receipts:
            directory = args.runtime / "calls" / r["id"]
            request_bytes = (directory / "request.json").read_bytes()
            assert digest(request_bytes) == r["request_sha256"]
            request = json.loads(request_bytes)
            if r["kind"] == "primary":
                expected_user = "Statements to judge:\n\n" + inputs[r["id"]]["statement"]
                assert request["messages"][1]["content"] == expected_user
                assert request["messages"][0]["content"] == (ROOT / "prompts/judge.md").read_text()
                assert r["id"] not in request["messages"][1]["content"]
            if "response_sha256" in r:
                raw = (directory / "response.json").read_bytes()
                assert digest(raw) == r["response_sha256"]
                response = json.loads(raw)
                message = response["choices"][0]["message"]["content"]
                assert digest(message.encode()) == r["content_sha256"]
                parsed = json.loads(message)
                assert parsed["status"] == r["status"]
                assert parsed["probability"] == r["probability"]
            if r["kind"] == "primary" and trace is None:
                trace = {k: r[k] for k in ("id", "input_sha256", "request_sha256", "response_sha256", "content_sha256", "status", "probability")}
    analysis = read(ROOT / "results/analysis.json")
    scored = read(ROOT / "results/scored_rows.json")
    tested = 0
    for split, report in analysis["splits"].items():
        rows = [r for r in scored if r["split"] == split]
        assert len(rows) == report["n_eligible"]
        for method, metrics in report["all_eligible_metrics"].items():
            ps, ys = [r["probabilities"][method] for r in rows], [r["label"] for r in rows]
            expected = {
                "brier": sum((p-y)**2 for p,y in zip(ps,ys))/len(rows),
                "log_loss": -sum(y*math.log(min(1-1e-6,max(1e-6,p)))+(1-y)*math.log(1-min(1-1e-6,max(1e-6,p))) for p,y in zip(ps,ys))/len(rows),
                "mean_absolute_error": sum(abs(p-y) for p,y in zip(ps,ys))/len(rows),
                "bias": sum(p-y for p,y in zip(ps,ys))/len(rows)}
            for metric, value in expected.items():
                assert abs(metrics[metric]-value) < 1e-12, (split,method,metric)
                tested += 1
    result = {"status":"verified", "primary_count":48, "preflight_count":1, "scalar_loss_checks":tested,
              "freeze_hashes_verified":len(freeze["files"]), "selection_precedes_test":True,
              "all_request_response_bytes_verified":args.runtime is not None, "trace":trace,
              "analysis_sha256":digest((ROOT/"results/analysis.json").read_bytes()),
              "verifier_sha256":digest(Path(__file__).read_bytes())}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
