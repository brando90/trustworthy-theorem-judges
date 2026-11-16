#!/usr/bin/env python3
"""Run one frozen source-only cell with a vendor's native agent CLI in an isolated container.

Harnesses: Google's Antigravity CLI (`agy`, Gemini 4 Argon) and xAI's Grok CLI (`grok`, Grok 4.7).
This generalizes claude_code_runner.py (same frozen v8 inputs, same source-only Lean image plus the
two CLIs, same preflight, same capture and receipt fields) so the four agents differ by vendor
harness and model, not by environment.

Isolation: the cell container has no mounts and sits on an internal Docker network whose only exit
is a CONNECT proxy that allows exact provider hostnames from the frozen condition and logs every
attempt (allowed or denied) as evidence. Credentials from the operator's own sign-in are streamed
into the container as its user (never printed, never committed).

Actions:
  proxy-server   (inside the proxy container) serve the allowlist from /allow.json
  network-setup  --condition C       create the internal network + proxy for C's allowlist
  auth-shell     --harness H --tag T  interactive container for the one-time sign-in; exports creds
  run            --condition C --condition-sha256 S --manifest M --task-id T --output-dir O --credentials D
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
PROJECT = "/home/user/lean_project"
HOME = "/home/user"
CRED_DIRS = {"antigravity": ".gemini", "grok": ".grok"}  # inside $HOME; confirmed by the auth-shell export
# Session transcripts the CLI writes (no credentials: Grok's login is ~/.grok/auth.json, outside sessions/).
# Grok's streaming JSON carries no model field, so model identity is read from these session files.
SESSION_DIRS = {"grok": f"{HOME}/.grok/sessions", "antigravity": None}
MODEL_FIELD = re.compile(r'"(?:model|model_id|modelId|model_name)"\s*:\s*"([^"]+)"')


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(Path(path).read_bytes())


def command(args, *, check=True, **kwargs):
    return subprocess.run(args, check=check, capture_output=True, text=True, **kwargs)


def write_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


# ---------------------------------------------------------------- proxy (runs inside its own container)
class LoggingProxy(http.server.BaseHTTPRequestHandler):
    """CONNECT only, port 443, exact allowlisted hostnames (or all, for sign-in discovery), public IPs only."""
    allow = json.loads(Path("/allow.json").read_text()) if Path("/allow.json").exists() else {"hosts": []}

    def log_message(self, *_):
        pass

    def record(self, host, decision):
        print(json.dumps({"t": time.time(), "host": host, "decision": decision}), flush=True)

    def do_CONNECT(self):
        try:
            hostname, port = self.path.rsplit(":", 1)
            allowed = self.allow.get("allow_all") or hostname in set(self.allow.get("hosts", []))
            if not allowed or port != "443":
                self.record(hostname, "deny")
                self.send_error(403)
                return
            addresses = socket.getaddrinfo(hostname, 443, type=socket.SOCK_STREAM)
            if not addresses or any(not ipaddress.ip_address(a[4][0]).is_global for a in addresses):
                self.record(hostname, "deny_non_public")
                self.send_error(403)
                return
            upstream = socket.create_connection((hostname, 443), timeout=20)
        except (ValueError, OSError):
            self.send_error(502)
            return
        self.record(hostname, "allow")
        self.send_response(200, "Connection established")
        self.end_headers()
        self.connection.settimeout(None)
        upstream.settimeout(None)
        with upstream, selectors.DefaultSelector() as selector:
            selector.register(self.connection, selectors.EVENT_READ, upstream)
            selector.register(upstream, selectors.EVENT_READ, self.connection)
            while True:
                ready = selector.select(timeout=300)
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
    Server(("0.0.0.0", 8080), LoggingProxy).serve_forever()


def net_names(tag: str) -> tuple[str, str]:
    assert re.fullmatch(r"[a-z0-9-]{2,40}", tag), "Unsafe network tag"
    return f"ttj-native2-{tag}", f"ttj-native2-egress-{tag}"


def setup_network(tag: str, allow: dict):
    network, proxy = net_names(tag)
    allow_bytes = (json.dumps(allow, sort_keys=True) + "\n").encode()
    label = sha_bytes(Path(__file__).read_bytes() + allow_bytes)
    found = command([DOCKER, "network", "inspect", network], check=False)
    if found.returncode:
        command([DOCKER, "network", "create", "--internal", network])
    else:
        assert json.loads(found.stdout)[0]["Internal"], "Network must be internal"
    found = command([DOCKER, "inspect", proxy], check=False)
    if found.returncode == 0:
        state = json.loads(found.stdout)[0]
        if state["Config"].get("Labels", {}).get("ttj.proxy.sha256") == label and state["State"]["Running"]:
            return network, proxy
        command([DOCKER, "rm", "-f", proxy])
    command([DOCKER, "create", "--name", proxy, "--network", network, "--label", f"ttj.proxy.sha256={label}",
             "--user", "65534:65534", "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
             "python:3.11-slim", "python", "/proxy.py", "proxy-server"])
    staging = Path(os.environ.get("TMPDIR", "/tmp")) / f"ttj_allow_{uuid.uuid4().hex}.json"
    staging.write_bytes(allow_bytes)
    try:
        command([DOCKER, "cp", str(Path(__file__).resolve()), f"{proxy}:/proxy.py"])
        command([DOCKER, "cp", str(staging), f"{proxy}:/allow.json"])
    finally:
        staging.unlink()
    command([DOCKER, "network", "connect", "bridge", proxy])
    command([DOCKER, "start", proxy])
    return network, proxy


# ---------------------------------------------------------------- cells
def load_cell(args):
    manifest_path = Path(args.manifest).resolve()
    condition_path = Path(args.condition).resolve()
    assert sha(condition_path) == args.condition_sha256, "Condition hash mismatch"
    condition = json.loads(condition_path.read_text())
    assert condition["status"] == "FROZEN", "Condition is not frozen"
    assert condition["input_manifest_sha256"] == sha(manifest_path), "Input manifest hash mismatch"
    assert condition["harness"] in CRED_DIRS, "Unknown harness"
    assert re.fullmatch(r"sha256:[a-f0-9]{64}", condition["docker_image"]), "Use an image digest"
    assert condition["max_attempts"] == 1 and isinstance(condition["max_task_seconds"], int)
    manifest = json.loads(manifest_path.read_text())
    assert manifest["schema_version"] == 2 and len(manifest["tasks"]) == 25, "Expected complete 25-task packet"
    matches = [t for t in manifest["tasks"] if t["task_id"] == args.task_id]
    assert len(matches) == 1 and re.fullmatch(r"[A-Za-z0-9_-]+", args.task_id), "Unknown or unsafe task ID"
    task = matches[0]
    visible = {}
    source_dir = Path(task["source_dir"]).resolve()
    for filename, expected_hash in task["files"].items():
        assert Path(filename).name == filename and Path(filename).suffix in {".py", ".md"}
        path = source_dir / filename
        assert path.is_file() and not path.is_symlink() and sha(path) == expected_hash, f"Changed {filename}"
        visible[path.name] = path
    assert len(visible) == 2 and task["prompt_file"] in visible
    output = task["expected_solver_output_path"]
    assert output.startswith(PROJECT + "/Veribench/") and Path(output).suffix == ".lean" and ".." not in Path(output).parts
    prompt = visible[task["prompt_file"]].read_text()
    assert ("Solve the entire assigned task" in prompt or "<!-- VeriBench strict-completion-v1 -->" in prompt)
    return condition, task, visible, prompt


def cli_command(condition, prompt_path: str):
    if condition["harness"] == "antigravity":
        return ["agy", "--print", "--model", condition["model"], "--effort", condition["effort"],
                "--dangerously-skip-permissions", "--disable-slash-commands", "--output-format", "stream-json",
                "--print-timeout", f"{condition['max_task_seconds']}s"]
    return ["grok", "--prompt-file", prompt_path, "--model", condition["model"],
            "--reasoning-effort", condition["effort"], "--always-approve", "--permission-mode", "bypassPermissions",
            "--max-turns", str(condition["max_turns"]), "--output-format", "streaming-json",
            "--disable-web-search", "--no-subagents", "--cwd", PROJECT]


def models_in(event, found: set):
    """Collect every model identifier the CLI reports anywhere in a stream event."""
    if isinstance(event, dict):
        for key, value in event.items():
            if key in ("model", "model_id", "modelId", "model_name") and isinstance(value, str):
                found.add(value)
            else:
                models_in(value, found)
    elif isinstance(event, list):
        for value in event:
            models_in(value, found)


def inject_credentials(container: str, harness: str, credentials: Path):
    """Stream the operator's credential directory in as the container user; contents are never printed."""
    assert credentials.is_dir() and credentials.stat().st_mode & 0o077 == 0, "Credentials dir must be owner-only"
    target = f"{HOME}/{CRED_DIRS[harness]}"
    tar = subprocess.Popen(["tar", "-C", str(credentials), "-cf", "-", "."], stdout=subprocess.PIPE)
    put = subprocess.run([DOCKER, "exec", "-i", container, "sh", "-c",
                          f"mkdir -p {target} && chmod 700 {target} && tar -C {target} -xf - && chmod -R go-rwx {target}"],
                         stdin=tar.stdout, capture_output=True)
    tar.stdout.close()
    assert tar.wait() == 0 and put.returncode == 0, "Credential injection failed"


def run_cell(args):
    condition, task, visible, prompt = load_cell(args)
    network, proxy = net_names(condition["network_tag"])
    prompt_path = f"/workspace/{task['prompt_file']}"
    planned = {"task_id": args.task_id, "condition_sha256": args.condition_sha256, "harness": condition["harness"],
               "command": cli_command(condition, prompt_path), "visible_files": {p.name: sha(p) for p in visible.values()},
               "output": task["expected_solver_output_path"], "model_call_performed": False}
    if args.dry_run:
        print(json.dumps(planned, indent=2))
        return
    out = Path(args.output_dir).resolve() / args.task_id
    out.mkdir(parents=True, exist_ok=False)  # a new invocation cannot silently retry a cell
    write_json(out / "planned.json", planned)
    assert json.loads(command([DOCKER, "network", "inspect", network]).stdout)[0]["Internal"]
    assert json.loads(command([DOCKER, "inspect", proxy]).stdout)[0]["State"]["Running"]
    container = f"ttj-{condition['harness'][:4]}-" + uuid.uuid4().hex[:12]
    proxy_url = f"http://{proxy}:8080"
    flags = [DOCKER, "create", "--name", container, "--network", network, "--cap-drop", "ALL",
             "--security-opt", "no-new-privileges", "--pids-limit", "512", "--memory", "8g", "--cpus", "2",
             "--workdir", PROJECT]
    for key, val in {"HTTPS_PROXY": proxy_url, "HTTP_PROXY": proxy_url, "https_proxy": proxy_url,
                     "http_proxy": proxy_url, "NO_PROXY": "", "DISABLE_AUTOUPDATER": "1",
                     "GROK_DISABLE_AUTOUPDATE": "1", "HOME": HOME}.items():
        flags += ["-e", f"{key}={val}"]
    flags += [condition["docker_image"], "sleep", "infinity"]
    command(flags)
    receipt = dict(planned, container=container, status="PREPARING")
    process = None
    started_wall = time.time()
    try:
        command([DOCKER, "start", container])
        inject_credentials(container, condition["harness"], Path(args.credentials).expanduser())
        command([DOCKER, "exec", container, "mkdir", "-p", "/workspace"])
        for filename, path in visible.items():
            data = path.read_bytes()
            put = subprocess.run([DOCKER, "exec", "-i", container, "sh", "-c", f"cat > /workspace/{filename}"],
                                 input=data, capture_output=True)
            assert put.returncode == 0, f"Could not stage {filename}"
        state = json.loads(command([DOCKER, "inspect", container]).stdout)[0]
        assert state["Mounts"] == [], "Unexpected host mount"
        assert set(state["NetworkSettings"]["Networks"]) == {network}
        binary = "agy" if condition["harness"] == "antigravity" else "grok"
        version = command([DOCKER, "exec", container, binary, "--version"]).stdout.strip()
        assert condition["cli_version"] in version, f"CLI version mismatch: {version}"
        preflight = command([DOCKER, "exec", container, "python3", "-c",
            "import os,pathlib; p=pathlib.Path('/home/user/lean_project'); "
            "assert os.getuid()==1001; assert not (p/'.lake/build').exists(); "
            "assert not (p/'.git').exists(); assert not list((p/'Veribench').iterdir()); "
            "q=pathlib.Path('/tmp/ttj_preflight.lean'); q.write_text('import Mathlib\\n#check Nat\\n'); "
            "import subprocess; subprocess.run(['lake','env','lean',str(q)],check=True); q.unlink(); "
            "assert not (p/'.lake/build').exists(); print('SOURCE_ONLY_USER1001_MATHLIB_PREFLIGHT_OK')"])
        receipt.update(cli_version=version, actual_mounts=[], network=network, proxy=proxy,
                       runtime_preflight=preflight.stdout.strip(), status="RUNNING", started_at=time.time(),
                       model_call_performed=True)
        write_json(out / "receipt.json", receipt)
        run = [DOCKER, "exec", "-i", "-w", PROJECT, container, *cli_command(condition, prompt_path)]
        process = subprocess.Popen(run, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        if condition["harness"] == "antigravity":
            process.stdin.write(prompt.encode())  # print mode reads the single prompt from stdin
        process.stdin.close()
        models, stop_reason, last_event = set(), None, None
        deadline = time.monotonic() + condition["max_task_seconds"] + 60
        buffer = b""
        with (out / "stream.jsonl").open("wb") as log, selectors.DefaultSelector() as selector:
            selector.register(process.stdout, selectors.EVENT_READ)
            while selector.get_map():
                if time.monotonic() >= deadline:
                    stop_reason = "wall_time_budget"
                    break
                for key, _ in selector.select(timeout=1):
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
                        models_in(event, models)
                        last_event = event
        if stop_reason:
            command([DOCKER, "stop", "--time", "2", container], check=False)
        returncode = process.wait(timeout=60)
        stop_reason = stop_reason or ("process_exit_0" if returncode == 0 else f"process_exit_{returncode}")
        command([DOCKER, "stop", "--time", "2", container], check=False)
        captured = command([DOCKER, "cp", f"{container}:{task['expected_solver_output_path']}",
                            str(out / "candidate.lean")], check=False)
        candidate = out / "candidate.lean"
        session_dir = SESSION_DIRS[condition["harness"]]
        if session_dir:
            copied = command([DOCKER, "cp", f"{container}:{session_dir}", str(out / "native_session")], check=False)
            for path in (out / "native_session").rglob("*") if copied.returncode == 0 else []:
                if path.is_file() and path.suffix == ".sqlite":
                    path.unlink()  # search index only; transcripts stay
                elif path.is_file():
                    models.update(MODEL_FIELD.findall(path.read_text(errors="replace")))
        egress = [json.loads(l) for l in command([DOCKER, "logs", "--since", str(int(started_wall)), proxy],
                                                  check=False).stdout.splitlines() if l.startswith("{")]
        expected = condition["model_identity_tokens"]
        receipt.update(status="TERMINAL", exit_code=returncode, stop_reason=stop_reason, finished_at=time.time(),
                       actual_models=sorted(models),
                       model_identity_verified=bool(models) and all(any(t in m for t in expected) for m in models),
                       last_event=last_event,
                       egress_hosts=sorted({e["host"] for e in egress}),
                       egress_denied=sorted({e["host"] for e in egress if e["decision"] != "allow"}),
                       candidate_captured=captured.returncode == 0,
                       candidate_sha256=sha(candidate) if candidate.exists() else None,
                       candidate_bytes=candidate.stat().st_size if candidate.exists() else None)
        write_json(out / "receipt.json", receipt)
    except BaseException as exc:
        if process and process.poll() is None:
            command([DOCKER, "stop", "--time", "2", container], check=False)
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        receipt.update(status="INFRASTRUCTURE_INTERRUPTED", error_type=type(exc).__name__, error=str(exc),
                       finished_at=time.time())
        write_json(out / "receipt.json", receipt)
        raise
    finally:
        command([DOCKER, "rm", "-f", container], check=False)
    print(json.dumps({k: receipt.get(k) for k in ["task_id", "status", "stop_reason", "candidate_sha256",
                                                    "actual_models", "egress_hosts"]}))


def auth_shell(args):
    """Interactive container for the one-time sign-in; afterwards export the credential dir (owner-only)."""
    network, proxy = net_names(args.tag)
    name = f"ttj-auth-{args.harness}"
    if args.export:
        target = Path(args.export).expanduser()
        target.mkdir(parents=True, exist_ok=True)
        os.chmod(target, 0o700)
        source = f"{HOME}/{CRED_DIRS[args.harness]}"
        tar = subprocess.Popen([DOCKER, "exec", name, "tar", "-C", source, "-cf", "-", "."], stdout=subprocess.PIPE)
        put = subprocess.run(["tar", "-C", str(target), "-xf", "-"], stdin=tar.stdout, capture_output=True)
        tar.stdout.close()
        assert tar.wait() == 0 and put.returncode == 0, "Export failed"
        for path in target.rglob("*"):
            os.chmod(path, 0o700 if path.is_dir() else 0o600)
        print(f"exported {sum(1 for p in target.rglob('*') if p.is_file())} credential files to {target}")
        return
    image = args.image
    command([DOCKER, "rm", "-f", name], check=False)
    proxy_url = f"http://{proxy}:8080"
    command([DOCKER, "create", "--name", name, "--network", network, "--cap-drop", "ALL",
             "--security-opt", "no-new-privileges", "-e", f"HTTPS_PROXY={proxy_url}", "-e", f"HTTP_PROXY={proxy_url}",
             "-e", f"https_proxy={proxy_url}", "-e", f"http_proxy={proxy_url}", "-e", f"HOME={HOME}",
             image, "sleep", "infinity"])
    command([DOCKER, "start", name])
    print(f"auth container {name} is up; sign in with:  docker exec -it {name} {'agy' if args.harness == 'antigravity' else 'grok login'}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    subs = parser.add_subparsers(dest="action", required=True)
    subs.add_parser("proxy-server")
    setup = subs.add_parser("network-setup")
    setup.add_argument("--condition")
    setup.add_argument("--tag")
    setup.add_argument("--allow-all", action="store_true", help="sign-in discovery only; never for cells")
    auth = subs.add_parser("auth-shell")
    auth.add_argument("--harness", choices=sorted(CRED_DIRS), required=True)
    auth.add_argument("--tag", required=True)
    auth.add_argument("--image", default="ttj-native-lean422-agy-grok:11-16-2026")
    auth.add_argument("--export")
    run = subs.add_parser("run")
    for name in ["manifest", "condition", "condition-sha256", "task-id"]:
        run.add_argument("--" + name, required=True)
    run.add_argument("--output-dir")
    run.add_argument("--credentials")
    run.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    if args.action == "proxy-server":
        serve_proxy()
    elif args.action == "network-setup":
        if args.condition:
            condition = json.loads(Path(args.condition).read_text())
            print(setup_network(condition["network_tag"], {"hosts": sorted(condition["allowed_hosts"])}))
        else:
            assert args.tag and args.allow_all, "Discovery networks need --tag and --allow-all"
            print(setup_network(args.tag, {"allow_all": True}))
    elif args.action == "auth-shell":
        auth_shell(args)
    else:
        if not args.dry_run and not (args.output_dir and args.credentials):
            parser.error("run requires --output-dir and --credentials")
        run_cell(args)


if __name__ == "__main__":
    main()
