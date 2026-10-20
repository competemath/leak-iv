"""The daemon against a fake `lake serve` (tests/fake_lake.py): the contract the
callers rely on, the recovery paths, and the fix for the 2026-10-20 outage (a
verify past the cap left the worker computing and every later script waited
behind it). No Lean, no network.

    python -m unittest discover -s tests -t . -v
"""
import asyncio
import base64
import json
import os
import shutil
import stat
import sys
import tempfile
import time
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def _make_world():
    """A temp dir with a `lake` shim on PATH, a project dir, and log files."""
    d = tempfile.mkdtemp(prefix="leak-iv-test-")
    bindir = os.path.join(d, "bin")
    os.makedirs(bindir)
    shim = os.path.join(bindir, "lake")
    with open(shim, "w") as f:
        f.write(f'#!/bin/sh\nexec "{sys.executable}" "{os.path.join(HERE, "fake_lake.py")}" "$@"\n')
    os.chmod(shim, os.stat(shim).st_mode | stat.S_IEXEC)
    project = os.path.join(d, "project")
    os.makedirs(project)
    env = {
        "PATH": bindir + os.pathsep + os.environ.get("PATH", ""),
        "LEAN_PROJECT_PATH": project,
        "FAKE_LAKE_LOG": os.path.join(d, "lake.log"),
        "FAKE_LAKE_WORKER_PID_FILE": os.path.join(d, "workers.txt"),
        "TENGOKU_AUTO_REFRESH": "0",
    }
    return d, env


# the module reads the environment when it is imported: set it first
_WORLD, _ENV = _make_world()
os.environ.update(_ENV)
sys.path.insert(0, ROOT)
import server  # noqa: E402

SUCCESS = "✅ Compilation Successful! The proof is 100% verified."


def lake_log():
    try:
        with open(_ENV["FAKE_LAKE_LOG"]) as f:
            return [json.loads(l) for l in f if l.strip()]
    except FileNotFoundError:
        return []


def worker_pids():
    try:
        with open(_ENV["FAKE_LAKE_WORKER_PID_FILE"]) as f:
            return [int(x) for x in f.read().split()]
    except FileNotFoundError:
        return []


def alive(pid):
    """Running, as against gone or a zombie waiting for its parent to reap it."""
    import subprocess
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    st = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
    return bool(st) and not st.startswith("Z")


class DaemonCase(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        for f in (_ENV["FAKE_LAKE_LOG"], _ENV["FAKE_LAKE_WORKER_PID_FILE"]):
            try:
                os.remove(f)
            except FileNotFoundError:
                pass
        self.d = server.LeanCompilerDaemon()
        await self.d.boot()

    async def asyncTearDown(self):
        for pid in worker_pids():
            try:
                os.kill(pid, 9)
            except ProcessLookupError:
                pass
        p = self.d.process
        if p and p.returncode is None:
            p.kill()
            try:
                await asyncio.wait_for(p.wait(), 5)
            except asyncio.TimeoutError:
                pass

    # ---- the contract the callers (the bridge, the memory) parse -----------------------------------------------------------------
    async def test_success_contract_and_import_injection(self):
        r = await self.d.verify_script("theorem t : True := trivial")
        self.assertTrue(r.startswith(SUCCESS), r)
        b64 = r.split("[[LEAK_NORMALIZED_SCRIPT_B64:")[1].split("]]")[0]
        compiled = base64.b64decode(b64).decode()
        self.assertTrue(compiled.startswith(server.TENGOKU_IMPORTS.split("\n")[0]), compiled)
        self.assertIn("theorem t : True := trivial", compiled)
        sent = [e for e in lake_log() if e["method"] == "textDocument/didOpen"][-1]["text"]
        self.assertTrue(sent.startswith(compiled.strip()), "what the marker carries is the user's part of what was compiled")
        self.assertIn("rogue axiom(s)", sent[len(compiled.strip()):], "followed by the axiom gate")

    async def test_the_axiom_closure_gate_is_sent_with_every_script_but_not_persisted(self):
        """The security gate (2026-10-07): without it `axiom cheat : False` followed by `cheat.elim` verified any
        statement. It is compiled after the user's script and is not part of the saved certificate."""
        r = await self.d.verify_script("theorem t : True := trivial")
        sent = [e for e in lake_log() if e["method"] in ("textDocument/didOpen", "textDocument/didChange")][-1]["text"]
        self.assertIn("rogue axiom(s) introduced by this script", sent)
        self.assertIn("env.constants", sent)
        self.assertTrue(sent.index("theorem t : True := trivial") < sent.index("run_cmd"), "the gate runs after the user's script")
        b64 = r.split("[[LEAK_NORMALIZED_SCRIPT_B64:")[1].split("]]")[0]
        self.assertNotIn("rogue axiom", base64.b64decode(b64).decode(), "the certificate is the user's script, not the gate")

    async def test_legacy_mathlib_import_is_rewritten_to_the_tree(self):
        r = await self.d.verify_script("import Mathlib\nimport Mathlib.Data.Nat.Basic\n\ntheorem t : True := trivial")
        self.assertTrue(r.startswith(SUCCESS), r)
        sent = [e for e in lake_log() if e["method"] in ("textDocument/didOpen", "textDocument/didChange")][-1]["text"]
        self.assertNotIn("import Mathlib", sent)
        self.assertIn("import Tengoku.Data.Nat.Basic", sent)

    async def test_sorry_is_a_failure(self):
        r = await self.d.verify_script("theorem t : True := by\n  sorry -- FAKE_SORRY")
        self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
        self.assertIn("Line 2 (Warning): declaration uses 'sorry'", r)

    async def test_error_lines_follow_the_grammar(self):
        r = await self.d.verify_script("theorem t : False := by\n  simp\n  -- FAKE_ERROR")
        self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
        self.assertIn("Line 3 (Error): unsolved goals ⊢ False", r)

    async def test_suggestions_are_harvested_without_touching_the_verdict(self):
        r = await self.d.verify_script("example (n : Nat) : n + 0 = n := by\n  exact?\n  -- FAKE_HINT")
        self.assertTrue(r.startswith(SUCCESS), r)
        self.assertIn("[[LEAK_SUGGESTIONS]]", r)
        self.assertIn("Suggestion @ line 4: Try this: exact Nat.add_zero n", r)
        self.assertNotRegex(r, r"Line \d+ \((Error|Warning)\)", "a hint is advisory: not in the error grammar")

    async def test_tool_wrapper_returns_the_daemons_answer(self):
        server.fast_compiler = self.d
        r = await server.verify_full_script("theorem t : True := trivial")
        self.assertTrue(r.startswith(SUCCESS), r)

    async def test_tengoku_sync_is_off_when_the_tree_is_a_working_copy(self):
        self.assertFalse(server.AUTO_REFRESH)
        r = await server.tengoku_sync()
        self.assertIn("disabled", r)

    # ---- the recovery paths -----------------------------------------------------------------------------------------------------------
    async def test_worker_crash_is_recovered_and_the_next_script_compiles(self):
        r = await self.d.verify_script("theorem t : True := by\n  decide -- FAKE_CRASH")
        self.assertIn("the Lean worker crashed", r)
        self.assertIn("self-healed", r)
        self.assertEqual(self.d.worker_restarts, 1)
        methods = [e["method"] for e in lake_log()]
        self.assertIn("textDocument/didClose", methods)
        r2 = await self.d.verify_script("theorem t2 : True := trivial")
        self.assertTrue(r2.startswith(SUCCESS), r2)
        self.assertEqual([e["method"] for e in lake_log()].count("textDocument/didOpen"), 2, "a fresh worker was opened")

    async def test_a_verify_past_the_cap_replaces_the_worker_so_the_next_script_is_not_stuck_behind_it(self):
        """The 2026-10-20 outage. Before the fix the stuck worker stayed, and every
        later script waited behind it for 25 minutes."""
        t0 = time.time()
        r = await self.d.verify_script("theorem big : True := by\n  decide +kernel -- FAKE_STUCK", timeout=2)
        self.assertLess(time.time() - t0, 8, "the cap is honoured")
        self.assertIn("verify exceeded 2s", r)
        self.assertIn("worker was stopped", r)
        self.assertIn("Do not resubmit", r)
        self.assertEqual(self.d.verify_timeouts, 1)
        self.assertEqual(self.d.worker_restarts, 1)
        pids = worker_pids()
        self.assertEqual(len(pids), 1)
        self.assertFalse(alive(pids[0]), "the worker that ignored `exit` was killed")
        methods = [e["method"] for e in lake_log()]
        self.assertIn("textDocument/didClose", methods)
        # the next script does not wait behind the old computation
        t1 = time.time()
        r2 = await self.d.verify_script("theorem small : True := trivial", timeout=10)
        self.assertTrue(r2.startswith(SUCCESS), r2)
        self.assertLess(time.time() - t1, 6)
        self.assertEqual(len(worker_pids()), 2, "a new worker was started for it")
        self.assertEqual(self.d.verify_timeouts, 1, "and it did not time out")

    async def test_a_script_queued_behind_a_stuck_one_waits_at_most_the_cap(self):
        stuck = asyncio.create_task(self.d.verify_script("theorem big : True := by\n  decide +kernel -- FAKE_STUCK", timeout=2))
        await asyncio.sleep(0.3)
        t0 = time.time()
        r = await self.d.verify_script("theorem small : True := trivial", timeout=10)
        self.assertTrue(r.startswith(SUCCESS), r)
        self.assertLess(time.time() - t0, 8, "the cap plus the respawn, not an open-ended wait")
        self.assertIn("verify exceeded 2s", await stuck)

    async def test_health_reports_the_counters(self):
        from starlette.testclient import TestClient
        server.fast_compiler = self.d
        await self.d.verify_script("theorem big : True := by\n  decide +kernel -- FAKE_STUCK", timeout=2)
        await self.d.verify_script("theorem t : True := trivial")
        with TestClient(server.build_app()) as c:
            h = c.get("/health").json()
        self.assertEqual(h["elaborator"], "up")
        self.assertEqual(h["verifies"], 2)
        self.assertEqual(h["verify_timeouts"], 1)
        self.assertEqual(h["worker_restarts"], 1)
        self.assertIsInstance(h["last_verify_ms"], int)
        self.assertEqual(h["verify_timeout_s"], server.VERIFY_TIMEOUT)
        self.assertFalse(h["busy"])


class ConstantsCase(unittest.TestCase):
    """Guardrails that exist because of earlier outages; a change that drops one should fail here."""

    def test_timeout_is_a_real_cap_and_configurable(self):
        self.assertGreaterEqual(server.VERIFY_TIMEOUT, 60)
        self.assertLessEqual(server.VERIFY_TIMEOUT, 600)
        self.assertIn("LEAK_VERIFY_TIMEOUT", open(os.path.join(ROOT, "server.py")).read())

    def test_crash_markers_and_watchdog_codes_are_kept(self):
        for m in ("stack overflow", "aborting", "panic", "segmentation fault"):
            self.assertIn(m, server._CRASH_MARKERS)
        self.assertIn(-32902, server._WORKER_DEAD_CODES)
        self.assertIn(-32900, server._WORKER_DEAD_CODES)

    def test_the_axiom_gate_allows_exactly_the_baseline_and_nothing_a_script_can_add(self):
        gate = server.AXIOM_CHECK
        # the trust set and the native_decide oracle ...
        for name in ("`propext", "`Classical.choice", "`Quot.sound", "`Lean.ofReduceBool", "`Lean.trustCompiler"):
            self.assertIn(name, gate)
        # ... and the markers Lean declares in every environment (the first deployment rejected `n + 0 = n := by simp` without them)
        for name in ("`sorryAx", "`lcAny", "`lcProof", "`lcErased", "`lcCast", "`lcVoid", "`lcUnreachable", "`Quot.lcInv", "`isScalarObj", "`Lean.ofReduceNat"):
            self.assertIn(name, gate)
        # it must still reject by throwing, and must look at axiom-kind constants only
        self.assertIn("throwError", gate)
        self.assertIn(".axiomInfo", gate)
        self.assertIn("allowed.contains n", gate)
        # the allowlist is a literal list of names, not something built from the script
        self.assertIn("let allowed : List Name :=", gate)

    def test_warmup_has_its_own_long_ceiling(self):
        self.assertGreaterEqual(server.WARMUP_TIMEOUT, 600)

    def test_the_tree_import_is_injected_by_default(self):
        self.assertTrue(server.TENGOKU_IMPORTS.startswith("import Tengoku"))

    def test_the_app_serves_refresh_and_health(self):
        app = server.build_app()
        paths = {getattr(r, "path", None) for r in app.routes}
        self.assertIn("/refresh", paths)
        self.assertIn("/health", paths)


if __name__ == "__main__":
    unittest.main()
