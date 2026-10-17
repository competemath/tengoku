#!/usr/bin/env python3
"""leak_canary.py [--space URL] [--file Canary.lean] [--known CanaryKnown.lean] — compile the canary on a Leak space and fail when it does not compile.

The canary (scripts/ci/canary/Canary.lean) is ordinary Lean and Mathlib that must elaborate under `import Tengoku.All`. A Leak space (`verify_full_script` over MCP/SSE, the same
tool the provers use) compiles it on its pinned tree; a failure is a library of the tree that leaks into everybody else (a global instance, notation or reserved word). Exit status:
0 compiled, 1 did not compile (the lines and messages are printed), 2 the space could not be asked (unreachable, timed out): a red run either way, with a different message.
CanaryKnown.lean (bugs known to be open) is compiled too and only reported.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import threading
import time
import urllib.request
from pathlib import Path
from urllib.parse import urljoin, urlsplit

HERE = Path(__file__).resolve().parent
DEFAULT_SPACE = "https://barkingtree-leak-iv.hf.space"
ERROR = re.compile(r"^Line (\d+) \((Error|Warning)\): (.*)$", re.M)
RETRY_PAUSE = 30  # seconds, times the number of the attempt that failed
MIN_CALL = 60  # an attempt that would get less than this is not started


class Unreachable(Exception):
    pass


LOCAL_HOSTS = ("127.0.0.1", "localhost", "::1")  # a server on this machine: the tests' fake space


def checked_space(url: str) -> str:
    """the origin of a Leak space: `https://host[:port]` (http only for a server on this machine), no credentials, no path, no query. A ValueError otherwise: the client
    sends the script it compiles to this address and follows the endpoint its stream names, so it must not be a `file:` URL or somebody else's host."""
    u = urlsplit(url.strip())
    if not (u.scheme == "https" or (u.scheme == "http" and u.hostname in LOCAL_HOSTS)):
        raise ValueError(f"the space must be an https URL (http only on this machine), not {url!r}")
    if not u.hostname or u.username or u.password or u.query or u.fragment or u.path not in ("", "/"):
        raise ValueError(f"the space must be an origin (https://host[:port]), not {url!r}")
    return f"{u.scheme}://{u.netloc}"


def call_tool(base: str, tool: str, args: dict, timeout: float = 900.0) -> str:
    """One MCP tool call over SSE: open the stream, take the message endpoint it names, initialize, call, read the reply from the stream."""
    base = checked_space(base)
    replies: dict[int, dict] = {}
    cond = threading.Condition()
    state: dict = {"endpoint": None, "dead": None}
    deadline = time.monotonic() + timeout

    def pump() -> None:
        try:
            req = urllib.request.Request(f"{base}/sse", headers={"accept": "text/event-stream"})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                event, data = None, []
                for raw in resp:
                    line = raw.decode("utf-8", "replace").rstrip("\r\n")
                    if line == "":
                        with cond:
                            if event == "endpoint":
                                endpoint = urljoin(f"{base}/", "\n".join(data))
                                if (
                                    urlsplit(endpoint)[:2] == urlsplit(base)[:2]
                                ):  # the same scheme and host: the stream does not send the script elsewhere
                                    state["endpoint"] = endpoint
                                else:
                                    state["dead"] = Unreachable(f"the stream names an endpoint on another host: {endpoint[:120]}")
                            elif event == "message":
                                try:
                                    msg = json.loads("\n".join(data))
                                    if isinstance(msg, dict) and msg.get("id") is not None:
                                        replies[msg["id"]] = msg
                                except ValueError:
                                    pass
                            cond.notify_all()
                        event, data = None, []
                    elif line.startswith("event:"):
                        event = line[6:].strip()
                    elif line.startswith("data:"):
                        data.append(line[5:].lstrip())
        except Exception as e:  # the stream ended or never opened
            with cond:
                state["dead"] = e
                cond.notify_all()

    threading.Thread(target=pump, daemon=True).start()

    def wait(pred) -> None:
        with cond:
            while not pred():
                if state["dead"] is not None and not pred():
                    raise Unreachable(f"{base}: the stream ended: {state['dead']!r}")
                left = deadline - time.monotonic()
                if left <= 0:
                    raise Unreachable(f"{base}: no answer in {timeout:.0f} s")
                cond.wait(min(left, 5))

    def post(body: dict) -> None:
        req = urllib.request.Request(
            state["endpoint"],
            data=json.dumps(body).encode(),
            headers={"content-type": "application/json"},
            method="POST",
        )
        try:
            urllib.request.urlopen(req, timeout=60).read()
        except Exception as e:
            raise Unreachable(f"{base}: POST failed: {e!r}") from e

    wait(lambda: state["endpoint"] is not None)
    post(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "protocolVersion": "2024-11-05",
                "capabilities": {},
                "clientInfo": {"name": "tengoku-canary", "version": "1"},
            },
        }
    )
    wait(lambda: 1 in replies)
    post({"jsonrpc": "2.0", "method": "notifications/initialized"})
    post(
        {
            "jsonrpc": "2.0",
            "id": 2,
            "method": "tools/call",
            "params": {"name": tool, "arguments": args},
        }
    )
    wait(lambda: 2 in replies)
    out = replies[2]
    if out.get("error"):
        raise Unreachable(f"{base}: {json.dumps(out['error'])[:300]}")
    return "\n".join(c.get("text", "") for c in (out.get("result") or {}).get("content", []))


def verdict(text: str) -> tuple[str, list[tuple[int, str]]]:
    """('ok' | 'failed' | 'infra', the (line, message) of every error): the reply of verify_full_script"""
    if "Compilation Successful" in text:
        return "ok", []
    errors = [(int(m.group(1)), m.group(3)) for m in ERROR.finditer(text) if m.group(2) == "Error"]
    if re.search(r"verify exceeded|timed out|timeout|Verification Error", text) and not errors:
        return "infra", []
    return ("failed" if errors or "Compilation Failed" in text else "infra"), errors


def report(name: str, script: str, errors: list[tuple[int, str]]) -> list[str]:
    src = script.split("\n")
    out = [f"{name}: {len(errors)} error(s)"]
    for n, msg in errors[:40]:
        out.append(f"  line {n}: {src[n - 1].strip()[:110] if 0 < n <= len(src) else '?'}\n    {msg[:220]}")
    return out


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--space", default=DEFAULT_SPACE)
    ap.add_argument("--file", default=str(HERE / "Canary.lean"))
    ap.add_argument("--known", default=str(HERE / "CanaryKnown.lean"))
    ap.add_argument("--timeout", type=float, default=900.0)
    ap.add_argument(
        "--retries",
        type=int,
        default=2,
        help="more attempts at the canary when the space could not be asked (the known-open file gets one)",
    )
    ap.add_argument(
        "--budget",
        type=float,
        default=1800.0,
        help="seconds for the whole run, retries and pauses included (the workflow's job must outlast it)",
    )
    a = ap.parse_args(argv)
    try:
        a.space = checked_space(a.space)
    except ValueError as e:
        ap.error(str(e))
    try:  # which tree the space has pinned, for the log
        with urllib.request.urlopen(f"{a.space}/refresh", timeout=60) as r:
            print("space:", r.read().decode()[:400])
    except Exception as e:
        print(f"space: /refresh not readable ({e!r})")
    results = {}
    start = time.monotonic()

    def left() -> float:
        return a.budget - (time.monotonic() - start)

    for label, path in (("canary", a.file), ("known open", a.known)):
        if not Path(path).is_file():
            continue
        script = Path(path).read_text(encoding="utf-8")
        tries = (
            a.retries + 1 if label == "canary" else 1
        )  # the known-open file is only reported: a slow space must not eat the canary's time
        for attempt in range(tries):
            if left() < MIN_CALL:
                kind, errors, text = "infra", [], f"the {a.budget:.0f} s budget of this run is used up"
                break
            try:
                text = call_tool(a.space, "verify_full_script", {"script": script}, min(a.timeout, left()))
                kind, errors = verdict(text)
            except Unreachable as e:
                kind, errors, text = "infra", [], str(e)
            if kind != "infra" or attempt == tries - 1:
                break
            time.sleep(max(0.0, min(RETRY_PAUSE * (attempt + 1), left())))
        results[label] = (kind, errors, script, text)
        print(f"{label}: {kind}")
        if kind == "failed":
            print("\n".join(report(label, script, errors)))
        if kind == "infra":
            print(f"  could not ask the space: {text[:300]}")
    kind = results.get("canary", ("infra",))[0]
    return {"ok": 0, "failed": 1}.get(kind, 2)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
