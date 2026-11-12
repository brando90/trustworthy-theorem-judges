#!/usr/bin/env python3
"""Run one frozen source-only Claude Code cell in an isolated Docker container.

No provider call is made by --help, network-setup, or dry-run. The condition binds
the complete input manifest, CLI/image/model/effort, and per-cell limits. The
coordinator owns the full 25-cell schedule and terminal reconciliation.
"""
from __future__ import annotations

import argparse
import hashlib
import http.server
import ipaddress
import json
import os
from pathlib import Path
import re
import selectors
import signal
import socket
import socketserver
import subprocess
import sys
import time
import uuid


DOCKER = os.environ.get("DOCKER", "docker")
NETWORK = "ttj-native-source-only"
PROXY = "ttj-native-egress"
PROXY_URL = f"http://{PROXY}:8080"
PROJECT = "/home/user/lean_project"
ALLOWED_HOSTS = {"api.anthropic.com", "generativelanguage.googleapis.com"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args, *, check=True, **kwargs):
    return subprocess.run(args, check=check, capture_output=True, text=True, **kwargs)


def write_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


class ProviderProxy(http.server.BaseHTTPRequestHandler):
    """CONNECT only, port 443, exact provider hostnames, public addresses only."""
    def log_message(self, *_):
        pass

    def do_CONNECT(self):
        try:
            hostname, port = self.path.rsplit(":", 1)
            if hostname not in ALLOWED_HOSTS or port != "443":
                self.send_error(403)
                return
            addresses = socket.getaddrinfo(hostname, 443, type=socket.SOCK_STREAM)
            if not addresses or any(not ipaddress.ip_address(a[4][0]).is_global for a in addresses):
                self.send_error(403)
                return
            upstream = socket.create_connection((hostname, 443), timeout=20)
        except (ValueError, OSError):
            self.send_error(502)
            return
        self.send_response(200, "Connection established")
        self.end_headers()
        self.connection.settimeout(None)
        upstream.settimeout(None)
        with upstream, selectors.DefaultSelector() as selector:
            selector.register(self.connection, selectors.EVENT_READ, upstream)
            selector.register(upstream, selectors.EVENT_READ, self.connection)
            while True:
                ready = selector.select(timeout=180)
                if not ready:
                    return
                for key, _ in ready:
                    try:
                        data = key.fileobj.recv(65536)
                        if not data:
                            return
                        key.data.sendall(data)
                    except OSError:
                        return


def serve_proxy():
    class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
        daemon_threads = True
    Server(("0.0.0.0", 8080), ProviderProxy).serve_forever()


def setup_network():
    found = command([DOCKER, "network", "inspect", NETWORK], check=False)
    if found.returncode:
        command([DOCKER, "network", "create", "--internal", NETWORK])
    else:
        assert json.loads(found.stdout)[0]["Internal"], "Network must be internal"
    found = command([DOCKER, "inspect", PROXY], check=False)
    if found.returncode == 0:
        state = json.loads(found.stdout)[0]
        expected = sha(Path(__file__))
        actual = state["Config"].get("Labels", {}).get("ttj.proxy.script_sha256")
        assert actual == expected, "Existing proxy uses different code; coordinate its owner"
        assert state["State"]["Running"], "Existing provider proxy is not running"
        return
    command([DOCKER, "create", "--name", PROXY, "--network", NETWORK,
             "--label", f"ttj.proxy.script_sha256={sha(Path(__file__))}",
             "--user", "65534:65534", "--cap-drop", "ALL",
             "--security-opt", "no-new-privileges", "python:3.11-slim",
             "python", "/proxy.py", "proxy-server"])
    command([DOCKER, "cp", str(Path(__file__).resolve()), f"{PROXY}:/proxy.py"])
    command([DOCKER, "network", "connect", "bridge", PROXY])
    command([DOCKER, "start", PROXY])


def load_cell(args):
    manifest_path = Path(args.manifest).resolve()
    condition_path = Path(args.condition).resolve()
    assert sha(condition_path) == args.condition_sha256, "Condition hash mismatch"
    condition = json.loads(condition_path.read_text())
    assert condition["status"] == "FROZEN", "Condition is not frozen"
    assert condition["input_manifest_sha256"] == sha(manifest_path), "Input manifest hash mismatch"
    assert condition["model"] == "claude-fable-5-1", "Pinned solver model changed"
    assert condition["effort"] == "max", "Pinned solver effort changed"
    assert re.fullmatch(r"sha256:[a-f0-9]{64}", condition["docker_image"]), "Use an image digest"
    assert condition["max_attempts"] == 1, "Runner supports one attempt per cell"
    for key in ["max_task_seconds", "max_turns", "max_total_tokens", "max_output_tokens", "max_response_tokens"]:
        assert isinstance(condition[key], int) and condition[key] > 0, key
    manifest = json.loads(manifest_path.read_text())
    assert len(manifest["tasks"]) == 25, "Expected complete 25-task packet"
    matches = [t for t in manifest["tasks"] if t["task_id"] == args.task_id]
    assert len(matches) == 1, "Task ID must identify exactly one frozen cell"
    task = matches[0]
    assert re.fullmatch(r"[A-Za-z0-9_-]+", args.task_id), "Unsafe task ID"
    assert manifest["schema_version"] == 2
    visible = {}
    source_dir = Path(task["source_dir"]).resolve()
    for filename, expected_hash in task["files"].items():
        assert Path(filename).name == filename and Path(filename).suffix in {".py", ".md"}
        path = source_dir / filename
        assert path.is_file() and not path.is_symlink(), "Expected regular source-only input"
        assert sha(path) == expected_hash, f"Changed {filename} bytes"
        visible[path.name] = path
    assert len(visible) == 2, "Source and instruction names collide"
    output = task["expected_solver_output_path"]
    assert output.startswith(PROJECT + "/Veribench/") and Path(output).suffix == ".lean"
    assert ".." not in Path(output).parts
    assert task["prompt_file"] in visible
    prompt = visible[task["prompt_file"]].read_text()
    assert ("Solve the entire assigned task" in prompt or
            "<!-- VeriBench strict-completion-v1 -->" in prompt), "Missing frozen completion reminder"
    return condition, task, visible, prompt


def cli_command(condition):
    return ["claude", "-p", "--safe-mode", "--dangerously-skip-permissions",
            "--permission-prompts", "none", "--model", condition["model"],
            "--effort", condition["effort"], "--max-turns", str(condition["max_turns"]),
            "--output-format", "stream-json", "--verbose", "--no-chrome",
            "--strict-mcp-config", "--mcp-config", '{"mcpServers":{}}',
            "--disable-slash-commands", "--tools", "Bash,Read,Write,Edit,Glob,Grep",
            "--disallowed-tools", "WebSearch,WebFetch,Agent,Task"]


def inspect_usage(event, seen):
    message = event.get("message", {})
    identity = message.get("id")
    usage = message.get("usage")
    if event.get("type") != "assistant" or not identity or not usage or identity in seen:
        return 0, 0
    seen.add(identity)
    output = int(usage.get("output_tokens", 0))
    total = output + sum(int(usage.get(k, 0)) for k in
                         ["input_tokens", "cache_creation_input_tokens", "cache_read_input_tokens"])
    return total, output


def run_cell(args):
    condition, task, visible, prompt = load_cell(args)
    planned = {"task_id": args.task_id, "condition_sha256": args.condition_sha256,
               "command": cli_command(condition), "visible_files": {p.name: sha(p) for p in visible.values()},
               "output": task["expected_solver_output_path"], "model_call_performed": False}
    if args.dry_run:
        print(json.dumps(planned, indent=2))
        return
    assert args.token_file, "Existing subscription grant file is required"
    token_path = Path(args.token_file)
    assert token_path.stat().st_mode & 0o077 == 0, "Grant must be owner-only"
    token = token_path.read_text().strip()
    assert re.fullmatch(r"sk-ant-oat\d{2}-[A-Za-z0-9_-]{32,}", token), "Not a setup-token grant"
    out = Path(args.output_dir).resolve() / args.task_id
    out.mkdir(parents=True, exist_ok=False)  # A new invocation cannot silently retry a cell.
    write_json(out / "planned.json", planned)
    assert json.loads(command([DOCKER, "network", "inspect", NETWORK]).stdout)[0]["Internal"]
    assert json.loads(command([DOCKER, "inspect", PROXY]).stdout)[0]["State"]["Running"]
    container = "ttj-cc-" + uuid.uuid4().hex[:12]
    env = os.environ.copy()
    env["CLAUDE_CODE_OAUTH_TOKEN"] = token
    flags = [DOCKER, "create", "--name", container, "--network", NETWORK,
             "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
             "--pids-limit", "512", "--memory", "8g", "--cpus", "2",
             "--workdir", PROJECT, "-e", "CLAUDE_CODE_OAUTH_TOKEN"]
    for key, val in {"HTTPS_PROXY": PROXY_URL, "HTTP_PROXY": PROXY_URL,
                     "https_proxy": PROXY_URL, "http_proxy": PROXY_URL,
                     "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC": "1", "DISABLE_AUTOUPDATER": "1",
                     "CLAUDE_CODE_MAX_OUTPUT_TOKENS": str(condition["max_response_tokens"]),
                     "ANTHROPIC_DEFAULT_OPUS_MODEL": condition["model"],
                     "ANTHROPIC_DEFAULT_SONNET_MODEL": condition["model"],
                     "ANTHROPIC_DEFAULT_HAIKU_MODEL": condition["model"],
                     "ANTHROPIC_SMALL_FAST_MODEL": condition["model"]}.items():
        flags += ["-e", f"{key}={val}"]
    flags += [condition["docker_image"], "sleep", "infinity"]
    command(flags, env=env)
    del env["CLAUDE_CODE_OAUTH_TOKEN"]
    token = None
    receipt = dict(planned, container=container, status="PREPARING", model_call_performed=False)
    process = None
    try:
        command([DOCKER, "start", container])
        for filename, path in visible.items():
            command([DOCKER, "cp", str(path), f"{container}:/workspace/{filename}"])
        # Container mount inspection proves that host repositories and credentials directories
        # are absent; only the short-lived process environment contains the subscription grant.
        state = json.loads(command([DOCKER, "inspect", container]).stdout)[0]
        assert state["Mounts"] == [], "Unexpected host mount"
        assert set(state["NetworkSettings"]["Networks"]) == {NETWORK}
        version = command([DOCKER, "exec", container, "claude", "--version"]).stdout.strip()
        assert version.split()[0] == condition["cli_version"], "CLI version mismatch"
        receipt.update(cli_version=version, actual_mounts=[], network=NETWORK,
                       status="RUNNING", started_at=time.time(), model_call_performed=True)
        write_json(out / "receipt.json", receipt)
        run = [DOCKER, "exec", "-i", container, *cli_command(condition)]
        process = subprocess.Popen(run, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        process.stdin.write(prompt.encode())
        process.stdin.close()
        seen, models, total_tokens, output_tokens = set(), set(), 0, 0
        stop_reason, final_event = None, None
        deadline = time.monotonic() + condition["max_task_seconds"]
        buffer = b""
        with (out / "stream.jsonl").open("wb") as log, selectors.DefaultSelector() as selector:
            selector.register(process.stdout, selectors.EVENT_READ)
            while selector.get_map():
                if time.monotonic() >= deadline:
                    stop_reason = "wall_time_budget"
                    break
                for key, _ in selector.select(timeout=min(1, max(0, deadline-time.monotonic()))):
                    data = os.read(key.fileobj.fileno(), 65536)
                    if not data:
                        selector.unregister(key.fileobj)
                        continue
                    log.write(data)
                    log.flush()
                    buffer += data
                    while b"\n" in buffer:
                        line, buffer = buffer.split(b"\n", 1)
                        try:
                            event = json.loads(line)
                        except (ValueError, UnicodeDecodeError):
                            continue
                        if not isinstance(event, dict):
                            continue
                        model = event.get("message", {}).get("model")
                        if model:
                            models.add(model)
                        if event.get("type") == "result":
                            final_event = event
                        delta, generated = inspect_usage(event, seen)
                        total_tokens += delta
                        output_tokens += generated
                        if total_tokens >= condition["max_total_tokens"]:
                            stop_reason = "observed_total_token_budget"
                        if output_tokens >= condition["max_output_tokens"]:
                            stop_reason = "observed_output_token_budget"
                    if stop_reason:
                        break
                if stop_reason:
                    break
        if stop_reason:
            command([DOCKER, "stop", "--time", "2", container], check=False)
        returncode = process.wait(timeout=30)
        if not stop_reason:
            stop_reason = "native_result" if final_event else "process_exit_without_result"
        # Stop every child write before capture. Compiler verification is separate from solver
        # generation and uses a fresh container with no provider network or credentials.
        command([DOCKER, "stop", "--time", "2", container], check=False)
        captured = command([DOCKER, "cp", f"{container}:{task['expected_solver_output_path']}", str(out / "candidate.lean")], check=False)
        candidate = out / "candidate.lean"
        receipt.update(status="TERMINAL", exit_code=returncode, stop_reason=stop_reason,
                       finished_at=time.time(), actual_models=sorted(models),
                       observed_total_tokens=total_tokens, observed_output_tokens=output_tokens,
                       usage_event_count=len(seen), native_result=final_event,
                       model_identity_verified=bool(models) and all(
                           m == condition["model"] or m.startswith(condition["model"] + "-")
                           for m in models),
                       candidate_captured=captured.returncode == 0,
                       candidate_sha256=sha(candidate) if candidate.exists() else None,
                       candidate_bytes=candidate.stat().st_size if candidate.exists() else None,
                       token_limit_note="Observed-response stop; an in-flight response can cross the threshold. Per-response output is separately capped.")
        write_json(out / "receipt.json", receipt)
    except BaseException as exc:
        if process and process.poll() is None:
            command([DOCKER, "stop", "--time", "2", container], check=False)
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        receipt.update(status="INFRASTRUCTURE_INTERRUPTED", error_type=type(exc).__name__,
                       error=str(exc), finished_at=time.time())
        command([DOCKER, "stop", "--time", "2", container], check=False)
        captured = command([DOCKER, "cp", f"{container}:{task['expected_solver_output_path']}", str(out / "candidate.lean")], check=False)
        candidate = out / "candidate.lean"
        receipt.update(candidate_captured=captured.returncode == 0,
                       candidate_sha256=sha(candidate) if candidate.exists() else None,
                       candidate_bytes=candidate.stat().st_size if candidate.exists() else None)
        write_json(out / "receipt.json", receipt)
        raise
    finally:
        command([DOCKER, "rm", "-f", container], check=False)
    print(json.dumps({k: receipt[k] for k in ["task_id", "status", "stop_reason", "candidate_sha256"]}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="action", required=True)
    subs.add_parser("proxy-server")
    subs.add_parser("network-setup")
    run = subs.add_parser("run")
    for name in ["manifest", "condition", "condition-sha256", "task-id"]:
        run.add_argument("--" + name, required=True)
    run.add_argument("--output-dir")
    run.add_argument("--token-file")
    run.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    if args.action == "proxy-server":
        serve_proxy()
    elif args.action == "network-setup":
        setup_network()
    else:
        if not args.dry_run and not args.output_dir:
            parser.error("run requires --output-dir")
        run_cell(args)


if __name__ == "__main__":
    main()
