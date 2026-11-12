#!/usr/bin/env python3
"""Run one frozen, source-only native Pi cell with an external cost gateway.

The solver container has only an internal Docker network. A separate gateway
container owns the provider key and admits only the frozen Google model. No
repository/home/gold volume is mounted. A failed cell is never retried here.

Prepare a manifest with `manifest`; freeze its printed SHA-256 in the parent
protocol, then pass it to `run --manifest-sha256`. `gateway` is an internal
subcommand used by the runner, not a general proxy. All receipts are private.
"""

from __future__ import annotations

import argparse
import hashlib
import http.server
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone

MODEL = "gemini-3.8-flash"
PROVIDER = "allen-google-veribench"
PI_VERSION = "1.5.2"
INPUT_PRICE = 0.75 / 1_000_000
OUTPUT_PRICE = 3.75 / 1_000_000
CELL_CAP = 0.75
REQUEST_CAP = 40
INPUT_TOKEN_CAP = 65_536
OUTPUT_TOKEN_CAP = 16_384
WALL_SECONDS = 1800
WORKSPACE = "/home/user/lean_project"
API_ROOT = "https://generativelanguage.googleapis.com/v1beta"
MAX_PAYLOAD_BYTES = 4_000_000
HTTP503_BACKOFF_SECONDS = (5, 15)


def now():
    return datetime.now(timezone.utc).isoformat()


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, obj):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")
    temp.replace(path)


def safe_relative(name):
    p = PurePosixPath(name)
    if not name or p.is_absolute() or ".." in p.parts or "." == name:
        raise ValueError(f"Unsafe relative path: {name!r}")
    return name


def freeze_input(args):
    root = Path(args.input_dir).resolve()
    paths = sorted(p for p in root.rglob("*") if p.is_file())
    if not paths or any(p.is_symlink() for p in root.rglob("*")):
        raise ValueError("Inputs must contain regular files and no symlinks")
    files = {str(p.relative_to(root)): sha256(p.read_bytes()) for p in paths}
    if args.prompt_file not in files:
        raise ValueError("Prompt file is not in input directory")
    safe_relative(args.output_file)
    if args.output_file in files:
        raise ValueError("Output must not exist among frozen inputs")
    manifest = {"task_id": args.task_id, "files": files,
                "prompt_file": args.prompt_file, "output_file": args.output_file,
                "source_only_approval": args.source_only_approval}
    write_json(args.manifest, manifest)
    print(json.dumps({"manifest": str(Path(args.manifest).resolve()),
                      "sha256": sha256(Path(args.manifest).read_bytes()),
                      "files": len(files)}))


def validate_manifest(path, expected_hash, root):
    raw = Path(path).read_bytes()
    if sha256(raw) != expected_hash:
        raise ValueError("Frozen manifest hash mismatch")
    manifest = json.loads(raw)
    if manifest.get("source_only_approval") is not True:
        raise ValueError("Manifest lacks source-only input approval")
    if not re.fullmatch(r"[A-Za-z0-9_-]+", manifest["task_id"]):
        raise ValueError("Invalid task ID")
    files = manifest["files"]
    if not files or manifest["prompt_file"] not in files:
        raise ValueError("Manifest has no input/prompt")
    for name, expected in files.items():
        safe_relative(name)
        source = root / name
        if source.is_symlink() or not source.resolve().is_relative_to(root):
            raise ValueError(f"Input escapes source directory: {name}")
        if sha256(source.read_bytes()) != expected:
            raise ValueError(f"Input hash mismatch: {name}")
    safe_relative(manifest["output_file"])
    if manifest["output_file"] in files:
        raise ValueError("Output already exists among input files")
    return manifest


class Budget:
    """Conservative ledger: no completed usage means no reservation refund."""

    def __init__(self, path):
        self.path = Path(path)
        if self.path.exists():
            raise ValueError("Ledger exists; each cell permits one attempt")
        self.data = {"started_at": now(), "model": MODEL,
                     "provider_route": PROVIDER, "cap_usd": CELL_CAP,
                     "input_price_per_million": INPUT_PRICE * 1_000_000,
                     "output_price_per_million": OUTPUT_PRICE * 1_000_000,
                     "requests": [], "denials": []}
        self.started = time.monotonic()
        self.save()

    def save(self):
        self.data["accounted_usd"] = sum(
            r.get("charged_upper_bound_usd", r["reserved_usd"])
            for r in self.data["requests"])
        write_json(self.path, self.data)

    def reserve(self, tokens, output_tokens, payload_hash):
        if time.monotonic() - self.started >= WALL_SECONDS:
            raise ValueError("Wall-clock budget exhausted")
        if len(self.data["requests"]) >= REQUEST_CAP:
            raise ValueError("Provider request cap reached")
        if not 0 < tokens <= INPUT_TOKEN_CAP:
            raise ValueError("Input token cap exceeded")
        if not 0 < output_tokens <= OUTPUT_TOKEN_CAP:
            raise ValueError("Output token cap exceeded")
        # Google countTokens excludes earlier thinking that generateContent
        # bills in subsequent promptTokenCount. Keep all prior billed thoughts
        # in the admission bound; do not silently treat countTokens as billing.
        prior_thoughts = sum(int(r.get("usage_metadata", {}).get("thoughtsTokenCount", 0))
                             for r in self.data["requests"])
        input_admission_bound = tokens + prior_thoughts + max(1024, (tokens + 9) // 10)
        if input_admission_bound > INPUT_TOKEN_CAP:
            raise ValueError("Input token cap exceeded")
        if any(r.get("provider_finish_reason") is None
               and not r.get("http503_before_response")
               for r in self.data["requests"]):
            raise ValueError("Earlier provider response incomplete; new admission stopped")
        # Reserve the FULL input capacity, not just the estimate. Cached input
        # is also reserved/charged at full price. Only complete actual usage
        # releases unused reservation; incomplete responses keep it all.
        reserved_input = INPUT_TOKEN_CAP
        reserved = reserved_input * INPUT_PRICE + output_tokens * OUTPUT_PRICE
        if self.data["accounted_usd"] + reserved > CELL_CAP + 1e-12:
            raise ValueError("Cell dollar cap cannot admit next request")
        row = {"call": len(self.data["requests"]) + 1,
               "admitted_at": now(), "counted_input_tokens": tokens,
               "prior_billed_thought_tokens": prior_thoughts,
               "input_admission_bound": input_admission_bound,
               "reserved_input_tokens": reserved_input,
               "max_output_tokens": output_tokens, "reserved_usd": reserved,
               "payload_sha256": payload_hash}
        self.data["requests"].append(row)
        self.save()
        return row

    def settle(self, row, usage, version, status, finish_reason=None):
        row["finished_at"] = now()
        row["http_status"] = status
        row["model_version"] = version
        row["provider_finish_reason"] = finish_reason
        if usage and "promptTokenCount" in usage:
            prompt = int(usage["promptTokenCount"])
            output = int(usage.get("candidatesTokenCount", 0)) + int(usage.get("thoughtsTokenCount", 0))
            row["usage_metadata"] = usage
            observed = prompt * INPUT_PRICE + output * OUTPUT_PRICE
            row["observed_cost_upper_bound_usd"] = observed
            if (prompt <= row["reserved_input_tokens"] and output <= row["max_output_tokens"]
                    and status == 200 and finish_reason is not None):
                row["charged_upper_bound_usd"] = observed
            else:
                row["provider_cap_violation"] = True
                row["charged_upper_bound_usd"] = max(row["reserved_usd"], observed)
        self.save()


def open_generation_with_503_recovery(budget, tokens, output_limit, body, request,
                                      opener=None, sleeper=None):
    """Retry only an HTTP 503 raised before response headers, twice at most.

    Every attempt reserves against the same cell ledger and 40-request cap.
    Failed reservations are never refunded. Stream/read failures are outside
    this helper and are not retried, since partial output may already exist.
    """
    opener = opener or urllib.request.urlopen
    sleeper = sleeper or time.sleep
    group_call = len(budget.data["requests"]) + 1
    for retry_index in range(len(HTTP503_BACKOFF_SECONDS) + 1):
        row = budget.reserve(tokens, output_limit, sha256(body))
        row["transport_group_first_call"] = group_call
        row["http503_retry_index"] = retry_index
        budget.save()
        try:
            return row, opener(request, timeout=180)
        except urllib.error.HTTPError as exc:
            if exc.code != 503:
                budget.settle(row, None, None, exc.code)
                raise
            row["http503_before_response"] = True
            row["transport_retry_exhausted"] = retry_index == len(HTTP503_BACKOFF_SECONDS)
            budget.settle(row, None, None, 503)
            budget.data["denials"].append({"at": now(), "reason": "HTTP503 before response",
                "phase": "generate_content", "upstream_http_status": 503,
                "call": row["call"], "retry_index": retry_index,
                "retry_exhausted": row["transport_retry_exhausted"]})
            budget.save()
            exc.close()
            if row["transport_retry_exhausted"]:
                raise
            delay = HTTP503_BACKOFF_SECONDS[retry_index]
            if time.monotonic() - budget.started + delay >= WALL_SECONDS:
                raise ValueError("Wall-clock budget exhausted")
            sleeper(delay)
        except Exception:
            budget.settle(row, None, None, 502)
            raise


def validated_payload(data):
    if not isinstance(data, dict) or "contents" not in data:
        raise ValueError("Expected native Google generateContent payload")
    if data.get("cachedContent"):
        raise ValueError("External cached content is not an allowed input")
    if set(data) - {"contents", "systemInstruction", "tools", "toolConfig", "generationConfig", "safetySettings"}:
        raise ValueError("Unexpected provider payload field")
    config = data.setdefault("generationConfig", {})
    requested = config.get("maxOutputTokens", OUTPUT_TOKEN_CAP)
    if not isinstance(requested, int) or isinstance(requested, bool) or not 0 < requested <= OUTPUT_TOKEN_CAP:
        raise ValueError("Output token limit differs from frozen cap")
    config["maxOutputTokens"] = requested
    if config.get("candidateCount", 1) != 1:
        raise ValueError("Exactly one candidate per native Pi request")
    if str(config.get("thinkingConfig", {}).get("thinkingLevel", "")).upper() != "HIGH":
        raise ValueError("Expected frozen HIGH thinking setting")
    for tool in data.get("tools", []):
        if set(tool) - {"functionDeclarations"}:
            raise ValueError("Only native Pi function tools are allowed")
    return data, requested


def serve_gateway(args):
    # Prices are frozen at the verified 11-11-2026 standard rate. Fail closed
    # after the announced price-change date rather than silently underbudget.
    if datetime.now(timezone.utc).date().isoformat() >= "2027-01-01":
        raise ValueError("Frozen provider price expired; new protocol required")
    key = os.environ.pop("GEMINI_API_KEY", "")
    if not key:
        raise ValueError("Gateway requires runtime GEMINI_API_KEY")
    budget = Budget(args.ledger)

    class Handler(http.server.BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.0"

        def log_message(self, *_):
            pass

        def fail(self, status, message):
            body = json.dumps({"error": {"code": status, "message": message}}).encode()
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):
            if self.path == "/health":
                self.send_response(200)
                self.end_headers()
                self.wfile.write(b"ready")
            else:
                self.fail(404, "Unsupported gateway route")

        def do_POST(self):
            row = None
            usage = None
            version = None
            finish_reason = None
            status = 502
            response_started = False
            phase = "validate_payload"
            try:
                parsed = urllib.parse.urlsplit(self.path)
                expected = f"/v1beta/models/{MODEL}:streamGenerateContent"
                if parsed.path != expected or urllib.parse.parse_qs(parsed.query) != {"alt": ["sse"]}:
                    raise ValueError("Provider model/operation differs from frozen condition")
                length = int(self.headers.get("Content-Length", "0"))
                if not 0 < length <= MAX_PAYLOAD_BYTES:
                    raise ValueError("Invalid or excessive payload size")
                data, output_limit = validated_payload(json.loads(self.rfile.read(length)))
                if any(r.get("provider_cap_violation") for r in budget.data["requests"]):
                    raise ValueError("Earlier provider cap violation; cell stopped")
                if len(budget.data["requests"]) >= REQUEST_CAP:
                    raise ValueError("Provider request cap reached")
                count_body = {"generateContentRequest": {"model": f"models/{MODEL}", **data}}
                phase = "count_tokens"
                request = urllib.request.Request(
                    f"{API_ROOT}/models/{MODEL}:countTokens",
                    data=json.dumps(count_body).encode(),
                    headers={"Content-Type": "application/json", "x-goog-api-key": key})
                with urllib.request.urlopen(request, timeout=60) as response:
                    tokens = int(json.load(response)["totalTokens"])
                body = json.dumps(data, separators=(",", ":")).encode()
                phase = "generate_content"
                request = urllib.request.Request(
                    API_ROOT + self.path[len("/v1beta"):], data=body,
                    headers={"Content-Type": "application/json", "x-goog-api-key": key})
                row, upstream = open_generation_with_503_recovery(
                    budget, tokens, output_limit, body, request)
                with upstream as response:
                    status = response.status
                    self.send_response(status)
                    self.send_header("Content-Type", "text/event-stream")
                    self.send_header("Cache-Control", "no-cache")
                    self.end_headers()
                    response_started = True
                    client_connected = True
                    for line in response:
                        if line.startswith(b"data: "):
                            try:
                                event = json.loads(line[6:])
                                usage = event.get("usageMetadata", usage)
                                version = event.get("modelVersion", version)
                                for candidate in event.get("candidates", []):
                                    finish_reason = candidate.get("finishReason", finish_reason)
                            except (ValueError, TypeError):
                                pass
                        if client_connected:
                            try:
                                self.wfile.write(line)
                                self.wfile.flush()
                            except (BrokenPipeError, ConnectionResetError):
                                client_connected = False
            except Exception as exc:
                # Never log provider error bodies, URLs with credentials, or
                # exception strings that might include sensitive headers.
                reason = str(exc) if isinstance(exc, ValueError) else type(exc).__name__
                denial = {"at": now(), "reason": reason, "phase": phase}
                if isinstance(exc, urllib.error.HTTPError):
                    denial["upstream_http_status"] = exc.code
                    if phase == "generate_content":
                        status = exc.code
                if isinstance(exc, urllib.error.URLError):
                    underlying = exc.reason
                    denial["underlying_error_type"] = type(underlying).__name__
                    if isinstance(getattr(underlying, "errno", None), int):
                        denial["underlying_errno"] = underlying.errno
                budget.data["denials"].append(denial)
                budget.save()
                if not response_started:
                    try:
                        self.fail(429 if isinstance(exc, ValueError) else 502, reason)
                    except (BrokenPipeError, ConnectionResetError):
                        pass
            finally:
                if row is not None:
                    budget.settle(row, usage, version, status, finish_reason)

    # HTTPServer serializes requests, preventing concurrent budget reservations.
    http.server.HTTPServer(("0.0.0.0", args.port), Handler).serve_forever()


def docker(*args, **kwargs):
    return subprocess.run(["docker", *args], check=True, capture_output=True, text=True, **kwargs)


def run_cell(args):
    root = Path(args.input_dir).resolve()
    manifest = validate_manifest(args.manifest, args.manifest_sha256, root)
    if not re.fullmatch(r"sha256:[0-9a-f]{64}", args.image):
        raise ValueError("Use the verified immutable Docker image ID")
    out = Path(args.output_dir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    lock = out / "attempt_started.json"
    with lock.open("x") as f:
        json.dump({"at": now(), "task_id": manifest["task_id"], "manifest_sha256": args.manifest_sha256}, f)
    image_info = json.loads(docker("image", "inspect", args.image).stdout)[0]
    # Scientific isolation relies on the accepted source-only image plus no
    # host/repository mounts and an internal-only network for the solver.
    receipt = {"started_at": now(), "task_id": manifest["task_id"],
               "manifest_sha256": args.manifest_sha256, "input_files": manifest["files"],
               "model": MODEL, "thinking": "high", "provider_route": PROVIDER,
               "pi_version_required": PI_VERSION, "image_id": image_info["Id"],
               "runner_sha256": sha256(Path(__file__).read_bytes()),
               "cell_cap_usd": CELL_CAP, "batch_25_cell_cap_usd": 25 * CELL_CAP,
               "request_cap": REQUEST_CAP, "input_token_cap": INPUT_TOKEN_CAP,
               "output_token_cap": OUTPUT_TOKEN_CAP, "wall_seconds": WALL_SECONDS,
               "transport_recovery": {"http503_before_response_retries": 2,
                                      "backoff_seconds": list(HTTP503_BACKOFF_SECONDS),
                                      "failed_reservations_retained": True,
                                      "native_pi_retries_enabled": False},
               "attempts": 1, "status": "preparing", "host_mounts": []}
    write_json(out / "receipt.json", receipt)
    suffix = sha256((str(out) + str(time.time_ns())).encode())[:12]
    network, gateway, solver = (f"ttj-pi-{x}-{suffix}" for x in ("net", "gateway", "solver"))
    created = []
    try:
        if not os.environ.get("GEMINI_API_KEY"):
            raise ValueError("Set GEMINI_API_KEY at runtime; runner never writes it to disk")
        docker("network", "create", "--internal", network)
        created.append(("network", network))
        # The gateway can reach Google. The solver can only reach this gateway.
        docker("create", "--name", gateway, "--network", "bridge", "--user", "root",
               "--env", "GEMINI_API_KEY", args.image, "python3", "/tmp/pi_runner.py",
               "gateway", "--ledger", "/tmp/gateway_ledger.json", env=os.environ.copy())
        created.append(("container", gateway))
        docker("network", "connect", "--alias", "provider-gateway", network, gateway)
        docker("cp", str(Path(__file__).resolve()), gateway + ":/tmp/pi_runner.py")
        docker("start", gateway)
        docker("create", "--name", solver, "--network", network,
               "--user", "user", "--workdir", WORKSPACE,
               "--env", "PI_CODING_AGENT_DIR=/tmp/pi-profile",
               "--env", "PI_OFFLINE=1", "--env", "PI_TELEMETRY=0",
               args.image, "sleep", "infinity")
        created.append(("container", solver))
        docker("start", solver)
        # A task-free image must not retain compiled benchmark modules from
        # its source project. Dependency caches are allowed; project caches
        # are not. Check before copying this cell's source files.
        clean_check = (
            "from pathlib import Path; "
            "p=Path('/home/user/lean_project'); "
            "assert not (p/'.git').exists(), 'project Git history present'; "
            "assert not (p/'.lake/build').exists(), 'compiled project artifacts present'; "
            "assert not any(x.is_file() for x in (p/'Veribench').rglob('*')), 'old task artifacts present'; "
            "unexpected=[str(x.relative_to(p)) for x in p.rglob('*') if x.is_file() "
            "and not str(x.relative_to(p)).startswith('.lake/packages/') "
            "and str(x.relative_to(p)) not in {'lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain'} "
            "and not str(x.relative_to(p)).startswith('.lake/lakefile.')]; "
            "assert not unexpected, 'unexpected project payload: '+repr(unexpected[:10]); "
            "print('clean source-only project')"
        )
        docker("exec", solver, "python3", "-c", clean_check)
        with tempfile.TemporaryDirectory(prefix="ttj-pi-stage-") as temp:
            stage = Path(temp)
            inputs = stage / "inputs"
            for name in manifest["files"]:
                destination = inputs / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(root / name, destination)
            profile = stage / "pi-profile"
            profile.mkdir()
            write_json(profile / "settings.json", {
                "defaultProvider": PROVIDER, "defaultModel": MODEL,
                "defaultThinkingLevel": "high", "cacheWarming": "off",
                "compaction": {"enabled": False},
                "retry": {"enabled": False, "maxRetries": 0,
                          "provider": {"maxRetries": 0, "timeoutMs": 180000}}})
            write_json(profile / "models.json", {"providers": {PROVIDER: {
                "baseUrl": "http://provider-gateway:8765/v1beta",
                "api": "google-generative-ai", "apiKey": "gateway-no-provider-secret",
                "models": [{"id": MODEL, "name": "Gemini 3.8 Flash (Allen VeriBench)",
                            "reasoning": True, "input": ["text"],
                            "contextWindow": INPUT_TOKEN_CAP, "maxTokens": OUTPUT_TOKEN_CAP,
                            "cost": {"input": 0.75, "output": 3.75,
                                     "cacheRead": 0.75, "cacheWrite": 0}}]}}})
            docker("cp", str(profile), solver + ":/tmp/pi-profile")
            docker("cp", str(inputs) + "/.", solver + ":" + WORKSPACE + "/")
        docker("exec", "--user", "root", solver, "chown", "-R", "user:user", "/tmp/pi-profile")
        # Keep the exact runtime user aligned with the accepted library Git
        # ownership. Lake can delete an otherwise valid checkout after Git's
        # dubious-ownership check prevents it from reading the origin URL.
        runtime_uid = docker("exec", solver, "id", "-u").stdout.strip()
        if runtime_uid != "1001":
            raise ValueError("Expected accepted image runtime user UID1001")
        receipt["runtime_uid"] = int(runtime_uid)
        version = docker("exec", solver, "pi", "--version").stdout.strip()
        receipt["pi_version_observed"] = version
        if version != PI_VERSION:
            raise ValueError("Native Pi version mismatch")
        isolation = json.loads(docker("inspect", solver).stdout)[0]
        if isolation["Mounts"] or set(isolation["NetworkSettings"]["Networks"]) != {network}:
            raise ValueError("Solver mounts/network differ from source-only contract")
        if not json.loads(docker("network", "inspect", network).stdout)[0]["Internal"]:
            raise ValueError("Solver network is not internal-only")
        # Wait for an actual responding gateway, not merely a live process.
        health = ["exec", solver, "python3", "-c",
                  "import urllib.request; print(urllib.request.urlopen('http://provider-gateway:8765/health',timeout=3).read().decode())"]
        for _ in range(30):
            try:
                if docker(*health).stdout.strip() == "ready":
                    break
            except subprocess.CalledProcessError:
                time.sleep(0.5)
        else:
            raise ValueError("Provider gateway did not become ready")
        receipt["status"] = "running"
        write_json(out / "receipt.json", receipt)
        command = ["docker", "exec", solver, "pi", "--provider", PROVIDER,
                   "--model", MODEL, "--thinking", "high", "--mode", "json", "--print",
                   "--no-context-files", "--no-extensions", "--no-mcp", "--no-skills",
                   "--no-prompt-templates", "--no-themes", "--offline", "--no-approve",
                   "--tools", "read,bash,edit,write", "--session-dir", "/tmp/pi-sessions",
                   "@" + WORKSPACE + "/" + manifest["prompt_file"]]
        started = time.monotonic()
        with (out / "trajectory.jsonl").open("wb") as stdout, (out / "stderr.log").open("wb") as stderr:
            process = subprocess.Popen(command, stdout=stdout, stderr=stderr)
            try:
                code = process.wait(timeout=WALL_SECONDS)
                receipt["status"] = "process_completed" if code == 0 else "process_failed"
                receipt["exit_code"] = code
            except subprocess.TimeoutExpired:
                receipt["status"] = "timeout"
                docker("stop", "--time", "2", solver)
                process.wait(timeout=15)
        receipt["elapsed_seconds"] = round(time.monotonic() - started, 3)
        # Native Pi can return process exit code zero after provider errors.
        # Preserve its semantic terminal status rather than claiming success.
        assistant_messages = []
        for line in (out / "trajectory.jsonl").read_text(errors="replace").splitlines():
            try:
                event = json.loads(line)
            except ValueError:
                continue
            if event.get("type") == "message_end" and event.get("message", {}).get("role") == "assistant":
                assistant_messages.append(event["message"])
        if assistant_messages:
            final = assistant_messages[-1]
            receipt["native_stop_reason"] = final.get("stopReason")
            receipt["actual_model"] = final.get("model")
            receipt["actual_provider"] = final.get("provider")
            receipt["actual_thinking"] = final.get("thinkingLevel")
            if receipt["status"] == "process_completed" and final.get("stopReason") in {"error", "aborted"}:
                receipt["status"] = "provider_error"
        elif receipt["status"] == "process_completed":
            receipt["status"] = "no_assistant_response"
        # A timeout/failed process can still leave an artifact: preserve it, never
        # relabel it as successful just because a file exists.
        candidate = out / "candidate.lean"
        try:
            docker("cp", solver + ":" + WORKSPACE + "/" + manifest["output_file"], str(candidate))
        except subprocess.CalledProcessError:
            receipt["artifact_status"] = "missing"
        else:
            if candidate.is_symlink() or not candidate.is_file():
                receipt["artifact_status"] = "invalid_nonregular_file"
            else:
                data = candidate.read_bytes()
                receipt["artifact_status"] = "present" if data.strip() else "empty"
                receipt["artifact_sha256"] = sha256(data)
                receipt["artifact_bytes"] = len(data)
                receipt["candidate_file"] = "candidate.lean"
        try:
            docker("cp", solver + ":/tmp/pi-sessions", str(out / "pi-sessions"))
        except subprocess.CalledProcessError:
            pass
    except Exception as exc:
        receipt["status"] = "runner_error"
        receipt["error_type"] = type(exc).__name__
        if isinstance(exc, ValueError):
            receipt["error"] = str(exc)
        raise
    finally:
        try:
            docker("cp", gateway + ":/tmp/gateway_ledger.json", str(out / "gateway_ledger.json"))
            ledger = json.loads((out / "gateway_ledger.json").read_text())
            receipt["provider_requests"] = len(ledger["requests"])
            receipt["accounted_usd"] = ledger["accounted_usd"]
        except (subprocess.CalledProcessError, FileNotFoundError):
            pass
        receipt["finished_at"] = now()
        write_json(out / "receipt.json", receipt)
        for kind, name in reversed(created):
            subprocess.run(["docker", kind, "rm", "-f", name] if kind == "container"
                           else ["docker", "network", "rm", name], capture_output=True)
    print(json.dumps(receipt, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    manifest = sub.add_parser("manifest", help="Write source allowlist for parent freezing")
    manifest.add_argument("--input-dir", required=True)
    manifest.add_argument("--task-id", required=True)
    manifest.add_argument("--prompt-file", required=True)
    manifest.add_argument("--output-file", default="candidate.lean")
    manifest.add_argument("--source-only-approval", action="store_true")
    manifest.add_argument("--manifest", required=True)
    run = sub.add_parser("run", help="Execute exactly one frozen cell")
    for name in ("input-dir", "manifest", "manifest-sha256", "image", "output-dir"):
        run.add_argument("--" + name, required=True)
    gateway = sub.add_parser("gateway", help=argparse.SUPPRESS)
    gateway.add_argument("--ledger", required=True)
    gateway.add_argument("--port", type=int, default=8765)
    args = parser.parse_args()
    {"manifest": freeze_input, "run": run_cell, "gateway": serve_gateway}[args.command](args)


if __name__ == "__main__":
    main()
