"""The canary (scripts/ci/canary): `import Tengoku.All` must stay usable. The client talks MCP over SSE to a Leak space; here against a fake one, and the files that run it are pinned
(the 2026-10-17 bug: lean-pool's global `prefix:80 "-"` made `-(3 * x)` on a real number "Ambiguous term", and its notations reserved `v`, `na`, `ω` as words, on Leak IV for days)."""

import http.server
import json
import queue
import re
import sys
import threading
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
CI = HERE.parent
ROOT = CI.parents[1]
sys.path.insert(0, str(CI / "canary"))
import leak_canary as lc  # noqa: E402

OK = "✅ Compilation Successful! The proof is 100% verified.\n[[LEAK_NORMALIZED_SCRIPT_B64:aW1wb3J0]]"
BAD = "❌ Compilation Failed:\nLine 3 (Error): Ambiguous term -(3 * x) Possible interpretations: a b\nLine 5 (Warning): unused\nLine 5 (Error): unexpected token 'v'; expected ')'\n"


def fake_space(reply, drop_stream=False):
    """a Leak space that answers verify_full_script with `reply(script)`; returns (server, base url, a function that ends the open streams)"""
    sessions: dict[str, queue.Queue] = {}
    counter = [0]

    class H(http.server.BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_GET(self):
            if self.path == "/refresh":
                body = b'{"status":"current","pinned":"abc"}'
                self.send_response(200)
                self.send_header("content-length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            counter[0] += 1
            sid = str(counter[0])
            sessions[sid] = q = queue.Queue()
            self.send_response(200)
            self.send_header("content-type", "text/event-stream")
            self.end_headers()
            self.wfile.write(f"event: endpoint\r\ndata: /messages/?session_id={sid}\r\n\r\n".encode())
            self.wfile.flush()
            if drop_stream:
                return
            while True:
                item = q.get()
                if item is None:
                    return
                self.wfile.write(f"event: message\r\ndata: {json.dumps(item)}\r\n\r\n".encode())
                self.wfile.flush()

        def do_POST(self):
            msg = json.loads(self.rfile.read(int(self.headers["content-length"])))
            q = sessions[self.path.rsplit("=", 1)[1]]
            self.send_response(202)
            self.send_header("content-length", "0")
            self.end_headers()
            if msg.get("method") == "initialize":
                q.put({"jsonrpc": "2.0", "id": msg["id"], "result": {}})
            elif msg.get("method") == "tools/call":
                text = reply(msg["params"]["arguments"]["script"])
                q.put(
                    {
                        "jsonrpc": "2.0",
                        "id": msg["id"],
                        "result": {"content": [{"type": "text", "text": text}]},
                    }
                )

    srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), H)
    srv.daemon_threads = True
    threading.Thread(target=srv.serve_forever, daemon=True).start()

    def close():
        for q in list(sessions.values()):
            q.put(None)

    return srv, f"http://127.0.0.1:{srv.server_address[1]}", close


class Client(unittest.TestCase):
    def run_main(self, space, tmp, **kw):
        c, k = Path(tmp) / "C.lean", Path(tmp) / "K.lean"
        c.write_text(
            "import Tengoku.All\nexample : True := trivial\nexample (x : ℝ) : -(3 * x) = -3 * x := by ring\nexample : True := trivial\nexample (v : ℕ) : True := trivial\n"
        )
        k.write_text("import Tengoku.All\nexample (resolve : ℕ) : True := trivial\n")
        return lc.main(
            [
                "--space",
                space,
                "--file",
                str(c),
                "--known",
                str(k),
                "--retries",
                "0",
                "--timeout",
                str(kw.get("timeout", 20)),
            ]
        )

    def test_a_script_that_compiles_exits_zero_and_one_that_does_not_exits_one(self):
        import tempfile

        for reply, want in ((lambda s: OK, 0), (lambda s: BAD, 1)):
            srv, base, close = fake_space(reply)
            try:
                with tempfile.TemporaryDirectory() as d:
                    self.assertEqual(self.run_main(base, d), want)
            finally:
                close()
                srv.shutdown()

    def test_the_known_open_file_is_reported_and_never_decides(self):
        import tempfile

        seen = []
        srv, base, close = fake_space(lambda s: (seen.append(s), BAD if "resolve" in s else OK)[1])
        try:
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(self.run_main(base, d), 0)
            self.assertEqual(len(seen), 2)  # the known-open file was asked as well, and its failure did not decide
        finally:
            close()
            srv.shutdown()

    def test_a_space_that_cannot_be_asked_exits_two_not_one(self):
        import tempfile

        srv, base, close = fake_space(lambda s: "", drop_stream=True)
        try:
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(self.run_main(base, d, timeout=5), 2)
        finally:
            srv.shutdown()
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(self.run_main("http://127.0.0.1:9", d, timeout=5), 2)

    def test_the_verdict_reads_the_replies_of_verify_full_script(self):
        self.assertEqual(lc.verdict(OK), ("ok", []))
        kind, errors = lc.verdict(BAD)
        self.assertEqual(kind, "failed")
        self.assertEqual([n for n, _ in errors], [3, 5])  # the warning is not an error
        self.assertEqual(lc.verdict("❌ Verification Error: verify exceeded 180s")[0], "infra")
        self.assertEqual(lc.verdict("")[0], "infra")

    def test_the_report_names_the_line_of_the_canary(self):
        out = "\n".join(
            lc.report(
                "canary",
                "a\nb\nexample (v : ℕ) : True := trivial\n",
                [(3, "unexpected token 'v'")],
            )
        )
        self.assertIn("line 3: example (v : ℕ)", out)


class QueueStep(unittest.TestCase):
    """the shell of the queue's canary step, run against a fake `lake` and a fake `git`: every mode and every outcome"""

    @staticmethod
    def step():
        import yaml

        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "queue-gate.yml").read_text(encoding="utf-8"))
        return next(s for s in wf["jobs"]["queue-build"]["steps"] if str(s.get("name", "")).startswith("Canary"))

    def run_step(self, lake_rc, var="", base_mode="report\n", base_has_file=True):
        import os
        import subprocess
        import tempfile

        with tempfile.TemporaryDirectory() as d:
            bin_ = Path(d) / "bin"
            bin_.mkdir()
            (bin_ / "lake").write_text(f"#!/bin/bash\necho 'Line 3 (Error): ambiguous' >&2; exit {lake_rc}\n")
            (bin_ / "git").write_text("#!/bin/bash\n" + (f"printf '%s' '{base_mode}'\n" if base_has_file else "exit 128\n"))
            (bin_ / "timeout").write_text('#!/bin/bash\nshift 2; shift; "$@"\n')  # timeout -k 30 3m CMD...
            for f in bin_.iterdir():
                f.chmod(0o755)
            env = {
                **os.environ,
                "PATH": f"{bin_}:{os.environ['PATH']}",
                "CANARY_MODE_VAR": var,
                "BASE_SHA": "a" * 40,
                "GITHUB_STEP_SUMMARY": str(Path(d) / "summary.md"),
            }
            r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", self.step()["run"]], cwd=d, env=env, capture_output=True, text=True)
            return r.returncode, r.stdout + r.stderr

    def test_report_mode_warns_and_lets_the_group_through(self):
        rc, out = self.run_step(1)
        self.assertEqual(rc, 0, out)
        self.assertIn("::warning::the canary does not compile", out)

    def test_enforce_mode_from_the_variable_or_from_the_base_fails_the_group(self):
        for kw in ({"var": "enforce"}, {"base_mode": "enforce\n"}):
            rc, out = self.run_step(1, **kw)
            self.assertEqual(rc, 1, (kw, out))
            self.assertIn("the tree is no longer usable", out)

    def test_a_canary_that_compiles_passes_in_every_mode(self):
        for kw in ({}, {"var": "enforce"}, {"base_mode": "enforce\n"}):
            self.assertEqual(self.run_step(0, **kw)[0], 0, kw)

    def test_the_variable_wins_over_the_base_file(self):
        self.assertEqual(self.run_step(1, var="report", base_mode="enforce\n")[0], 0)

    def test_a_missing_mode_file_is_report_and_an_unknown_word_is_an_error(self):
        self.assertEqual(self.run_step(1, base_has_file=False)[0], 0)
        rc, out = self.run_step(1, base_mode="Enforce\n")
        self.assertEqual(rc, 1)
        self.assertIn("unknown canary mode", out)

    def test_no_verdict_in_time_is_a_warning_even_when_enforcing(self):
        for rc_lake in (124, 137):
            rc, out = self.run_step(rc_lake, var="enforce")
            self.assertEqual(rc, 0, out)
            self.assertIn("did not finish in 3 minutes", out)

    def test_it_runs_whenever_the_library_built_and_not_when_it_did_not(self):
        s = self.step()
        self.assertIn("steps.delta.outputs.built == 'yes'", s["if"])
        self.assertNotIn("needs-nightly", s["if"])  # a delta too big to publish has nothing to do with whether the tree is usable
        wf = (ROOT / ".github" / "workflows" / "queue-gate.yml").read_text(encoding="utf-8")
        self.assertIn('echo "built=$([ "$rc" = 0 ] && echo yes || echo no)" >> "$GITHUB_OUTPUT"', wf)


class Files(unittest.TestCase):
    """What the canary must keep catching: one probe per kind of failure that has happened."""

    def setUp(self):
        self.canary = (CI / "canary" / "Canary.lean").read_text(encoding="utf-8")

    def test_it_imports_the_whole_tree_and_sets_the_options_that_keep_it_honest(self):
        self.assertTrue(self.canary.startswith("import Tengoku.All\n"))
        self.assertIn("set_option Elab.async false", self.canary)  # errors come back on the line that has them

    def test_notation_words_and_tactics_are_all_probed(self):
        for probe in (
            "-(3 * x) = -3 * x",  # lean-pool Modal: prefix:80 "-"
            "(f ∘ g) 0",
            "x⁻¹ * x = 1",
            "Real.sqrt 4 = 2",
            "3 ∈ insert 5 s",
            "l[0] = l[0]",
            "a ≃ b",
            "X ⟶ Y",
            "X ≅ X",
            "a b c d e f g h i j k l m n o p q r s t u v w x y z",  # `v` was a reserved word
            "(na ih hx",
            "Δ ω",
            "by omega",
            "by positivity",
            "by linarith",
            "by nlinarith",
            "by ring",
            "by field_simp",
            "by norm_num",
            "by gcongr",
            "by fun_prop",
            "by interval_cases",
            "by decide",
            "by simp",
        ):
            self.assertIn(probe, self.canary, probe)

    def test_what_is_not_fixed_yet_is_in_the_known_open_file_not_in_the_gate(self):
        known = (CI / "canary" / "CanaryKnown.lean").read_text(encoding="utf-8")
        for word in (
            "resolve",
            "superpose",
            "Facts",
            "memoFinOp",
            "finOpTable",
            "mod_symm",
        ):
            self.assertIn(f"({word} : ℕ)", known)
            self.assertNotIn(word, self.canary)

    def test_the_queue_runs_it_after_the_library_is_built_and_it_can_be_made_to_fail_the_group(
        self,
    ):
        wf = (ROOT / ".github" / "workflows" / "queue-gate.yml").read_text(encoding="utf-8")
        i = wf.index("name: Canary")
        step = wf[i : wf.index("\n      - ", i + 10)]
        self.assertIn("merge_group", step)
        self.assertIn("scripts/ci/canary/Canary.lean", step)
        self.assertIn("enforce", step)
        self.assertLess(
            wf.index("name: Build the library as main will have it"),
            i,
            "the tree is built before the canary imports it",
        )

    def test_the_leak_space_is_asked_on_a_schedule_and_after_every_promotion(self):
        wf = (ROOT / ".github" / "workflows" / "leak-canary.yml").read_text(encoding="utf-8")
        self.assertIn("schedule:", wf)
        self.assertIn("topup-promote", wf)
        self.assertIn("leak_canary.py", wf)
        self.assertNotIn("secrets.", wf)  # the space is public; nothing here needs a token
        self.assertTrue(re.search(r"permissions:\s*\{\s*\}", wf) or "permissions: {}" in wf)


if __name__ == "__main__":
    unittest.main()
