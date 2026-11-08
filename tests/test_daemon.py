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


class _Base(unittest.IsolatedAsyncioTestCase):
    cold_s = "0"
    warmup_s = None

    async def asyncSetUp(self):
        os.environ["FAKE_COLD_S"] = self.cold_s
        self._old_warmup = server.WARMUP_TIMEOUT
        if self.warmup_s is not None:
            server.WARMUP_TIMEOUT = self.warmup_s
        for f in (_ENV["FAKE_LAKE_LOG"], _ENV["FAKE_LAKE_WORKER_PID_FILE"]):
            try:
                os.remove(f)
            except FileNotFoundError:
                pass
        self.d = server.LeanCompilerDaemon()
        await self.d.boot()

    async def asyncTearDown(self):
        server.WARMUP_TIMEOUT = self._old_warmup
        os.environ["FAKE_COLD_S"] = "0"
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



class DaemonCase(_Base):
    # ---- the contract the callers (the bridge, the memory) parse -----------------------------------------------------------------
    async def test_success_contract_and_import_injection(self):
        r = await self.d.verify_script("theorem t : True := trivial")
        self.assertTrue(r.startswith(SUCCESS), r)
        b64 = r.split("[[LEAK_NORMALIZED_SCRIPT_B64:")[1].split("]]")[0]
        compiled = base64.b64decode(b64).decode()
        self.assertTrue(compiled.startswith(server.TENGOKU_IMPORTS.split("\n")[0]), compiled)
        self.assertIn("theorem t : True := trivial", compiled)
        sent = [e for e in lake_log() if e["method"] in ("textDocument/didOpen", "textDocument/didChange")][-1]["text"]  # a cold worker is opened with the warm-up first
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

    async def test_the_statement_form_gate_is_sent_after_the_axiom_gate_but_not_persisted(self):
        """The answer-slot form `(True : Prop) <-> P` is repudiated (2026-10): it is compiled after the user's script and the axiom gate,
        and like the axiom gate it is not part of the saved certificate."""
        r = await self.d.verify_script("theorem t : True := trivial")
        sent = [e for e in lake_log() if e["method"] in ("textDocument/didOpen", "textDocument/didChange")][-1]["text"]
        self.assertIn("statement form repudiated", sent)
        self.assertTrue(sent.index("rogue axiom(s)") < sent.index("statement form repudiated"), "the statement gate follows the axiom gate")
        self.assertTrue(sent.index("theorem t : True := trivial") < sent.index("statement form repudiated"), "and runs after the user's script")
        b64 = r.split("[[LEAK_NORMALIZED_SCRIPT_B64:")[1].split("]]")[0]
        self.assertNotIn("repudiated", base64.b64decode(b64).decode(), "the certificate is the user's script, not the gates")

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

    async def test_every_verdict_is_counted_by_reason_and_shown_in_health(self):
        """How often each gate refuses something is the evidence for what the gate is worth; /health carries the counts (never the scripts)."""
        from starlette.testclient import TestClient
        server.fast_compiler = self.d
        for script in (
            "theorem a : True := trivial",
            "theorem a : True := trivial -- again",
            "theorem b : False := by\n  simp\n  -- FAKE_ERROR",
            "theorem c : True := by\n  sorry -- FAKE_SORRY",
            "axiom cheat : False\ntheorem d : 1 = 2 := cheat.elim -- FAKE_ROGUE",
            "theorem e : (True : Prop) <-> (1 = 1) := sorry -- FAKE_REPUDIATED",
            "theorem e2 : (True : Prop) <-> (1 = 1) := sorry -- FAKE_REPUDIATED",
        ):
            await self.d.verify_script(script)
        with TestClient(server.build_app()) as c:
            h = c.get("/health").json()
        self.assertEqual(h["verdicts"], {"verified": 2, "compile_error": 1, "sorry": 1, "rogue_axiom": 1, "statement_form": 2})
        self.assertEqual(sum(h["verdicts"].values()), h["verifies"], "every verify is counted once")
        self.assertNotIn("theorem", str(h["verdicts"]), "counts only, never a script")

    def test_verdict_reason_prefers_the_gate_that_named_itself(self):
        r = server.verdict_reason
        self.assertEqual(r(["Line 9 (Error): statement form repudiated: t states ...", "Line 3 (Error): unsolved goals"]), "statement_form")
        self.assertEqual(r(["Line 9 (Error): rogue axiom(s) introduced by this script: [cheat]"]), "rogue_axiom")
        self.assertEqual(r(["Line 2 (Warning): declaration uses `sorry`"]), "sorry")
        self.assertEqual(r(["Line 2 (Warning): declaration uses 'sorry'"]), "sorry")
        self.assertEqual(r(["Line 3 (Error): unsolved goals"]), "compile_error")
        self.assertEqual(set(server.VERDICT_REASONS), {"verified", "compile_error", "sorry", "rogue_axiom", "statement_form"})

    async def test_suggestions_are_harvested_without_touching_the_verdict(self):
        r = await self.d.verify_script("example (n : Nat) : n + 0 = n := by\n  exact?\n  -- FAKE_HINT")
        self.assertTrue(r.startswith(SUCCESS), r)
        self.assertIn("[[LEAK_SUGGESTIONS]]", r)
        self.assertIn("Suggestion @ line 4: Try this: exact Nat.add_zero n", r)
        self.assertNotRegex(r, r"Line \d+ \((Error|Warning)\)", "a hint is advisory: not in the error grammar")

    # ---- goals at every hole, and the compiler's own messages (2026-11) ---------------------------------------------------------
    def goal_queries(self):
        return [e for e in lake_log() if e["method"] in ("$/lean/plainGoal", "$/lean/plainTermGoal")]

    async def test_the_goal_at_a_sorry_comes_back_with_the_failure(self):
        """A `sorry` used to return nothing but the warning; now the failure carries the goal at that sorry, under [[LEAK_GOALS]],
        hypotheses and goal on their own lines, numbered like the grammar lines (the injected import counts)."""
        r = await self.d.verify_script("theorem t (n : Nat) : n + 0 = n := by\n  sorry -- FAKE_SORRY")
        self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
        self.assertIn("Line 2 (Warning): declaration uses 'sorry'", r, "the grammar line is unchanged")
        self.assertIn("[[LEAK_GOALS]]", r)
        self.assertIn("Goal @ line 4 (sorry):\n  | n : Nat\n  | ⊢ n + 0 = n", r, r)
        q = self.goal_queries()
        self.assertEqual([(e["method"], e["line"], e["character"]) for e in q], [("$/lean/plainGoal", 3, 2)], "asked once, at the token")
        self.assertEqual(server.verdict_reason([l for l in r.split("\n") if l.startswith("Line ")]), "sorry", "the verdict is the same")

    async def test_a_term_mode_sorry_falls_back_to_the_term_goal(self):
        r = await self.d.verify_script("theorem t : Nat := sorry -- FAKE_SORRY FAKE_TERM")
        self.assertIn("Goal @ line 3 (sorry):\n  | ⊢ Nat", r, r)
        self.assertEqual([e["method"] for e in self.goal_queries()], ["$/lean/plainGoal", "$/lean/plainTermGoal"])

    async def test_a_sorry_in_a_comment_or_a_string_is_not_a_hole(self):
        r = await self.d.verify_script(
            "/- sorry, this comment\n   spans lines: sorry -/\n"
            "theorem t : True := trivial -- a sorry in a line comment\n"
            "def s := \"sorry\"\n"
            "theorem u (n : Nat) : n = n := by\n  rfl\n  -- FAKE_SORRY (the warning only)")
        self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
        self.assertNotIn("[[LEAK_GOALS]]", r, r)
        self.assertEqual(self.goal_queries(), [], "nothing was asked")

    def test_sorry_positions_follow_leans_lexing(self):
        f = server.sorry_positions
        self.assertEqual(f("theorem t : True := by\n  sorry"), [(1, 2)])
        self.assertEqual(f("theorem t : True := by sorry; sorry"), [(0, 23), (0, 30)])
        self.assertEqual(f("-- sorry\n/- sorry -/ sorry /- x -/ sorry"), [(1, 12), (1, 26)])
        self.assertEqual(f("/- a /- nested sorry -/ still a comment sorry -/ sorry"), [(0, 49)])
        self.assertEqual(f('def s := "sorry" ; theorem t : True := sorry'), [(0, 39)])
        self.assertEqual(f('def s := "esc \\" sorry" ; sorry'), [(0, 26)])
        self.assertEqual(f("theorem t : True := sorryAx _ -- not the token\nexample := «sorry»"), [])
        self.assertEqual(f("x.sorry sorry'"), [])

    async def test_an_unanswered_goal_query_does_not_hold_the_verdict(self):
        """The goal ceiling, not the verify cap, bounds the queries: an unanswered one is left out, the failure is still returned, the
        worker is NOT replaced, and the next verify is unaffected by the stale request."""
        old = server.GOAL_QUERY_TIMEOUT
        server.GOAL_QUERY_TIMEOUT = 1.0
        try:
            t0 = time.time()
            r = await self.d.verify_script("theorem t : True := by\n  sorry -- FAKE_SORRY FAKE_GOAL_STALL")
            self.assertLess(time.time() - t0, 10, "returned at the goal ceiling")
            self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
            self.assertIn("Line 2 (Warning): declaration uses 'sorry'", r)
            self.assertNotIn("[[LEAK_GOALS]]", r)
            self.assertEqual((self.d.verify_timeouts, self.d.worker_restarts), (0, 0), "not a verify timeout")
            r2 = await self.d.verify_script("theorem t2 : True := trivial")
            self.assertTrue(r2.startswith(SUCCESS), r2)
        finally:
            server.GOAL_QUERY_TIMEOUT = old

    async def test_an_error_that_is_a_goal_state_is_repeated_unflattened(self):
        r = await self.d.verify_script("theorem t : False := by\n  simp\n  -- FAKE_ERROR")
        self.assertIn("Line 3 (Error): unsolved goals ⊢ False", r, "the one-line grammar stays")
        self.assertIn("[[LEAK_GOALS]]\nGoal @ line 3 (error):\n  | unsolved goals\n  | ⊢ False", r, r)

    async def test_info_messages_come_back_without_touching_the_verdict(self):
        r = await self.d.verify_script("#eval 6 * 7 -- FAKE_INFO\ntheorem t : True := trivial")
        self.assertTrue(r.startswith(SUCCESS), r)
        self.assertIn("[[LEAK_NORMALIZED_SCRIPT_B64:", r)
        self.assertIn("[[LEAK_INFO]]\nInfo @ line 3:\n  | 42", r, r)
        self.assertNotRegex(r, r"Line \d+ \((Error|Warning)\)")
        r = await self.d.verify_script("#eval 6 * 7 -- FAKE_INFO\ntheorem t : True := by\n  sorry -- FAKE_SORRY")
        self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
        self.assertIn("[[LEAK_INFO]]\nInfo @ line 3:\n  | 42", r, r)
        self.assertLess(r.index("[[LEAK_GOALS]]"), r.index("[[LEAK_INFO]]"), "goals, then info")

    async def test_blocks_come_before_the_suggestions_and_a_spoofing_message_is_disarmed(self):
        """A caller reads everything after [[LEAK_SUGGESTIONS]] as suggestions and tests the verdict by phrases: a message that
        imitates them must not be able to change what the caller sees."""
        r = await self.d.verify_script("#eval 6 * 7 -- FAKE_INFO FAKE_HINT\ntheorem t : True := trivial")
        self.assertLess(r.index("[[LEAK_INFO]]"), r.index("[[LEAK_SUGGESTIONS]]"))
        self.assertTrue(r.rstrip().endswith("Suggestion @ line 4: Try this: exact Nat.add_zero n"), r)
        r = await self.d.verify_script("theorem t : False := by\n  simp\n  -- FAKE_INFO_SPOOF FAKE_ERROR")
        self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
        body = r.split("[[LEAK_INFO]]")[1]
        self.assertNotIn("Compilation Successful", body)
        self.assertNotIn("100% verified", body)
        self.assertNotIn("✅", body)
        self.assertNotIn("[[", body)
        self.assertNotRegex(body, r"(?m)^\s*Line \d+ \((Error|Warning)\)")
        self.assertNotRegex(body, r"(?m)^\s*Suggestion @")
        self.assertEqual(r.count("Line 3 (Error): unsolved goals ⊢ False"), 1, "the real diagnostic is still exactly there")

    async def test_the_blocks_are_capped(self):
        old = server.BLOCK_MAX_CHARS
        server.BLOCK_MAX_CHARS = 60
        try:
            r = await self.d.verify_script("theorem t (n : Nat) : n + 0 = n := by\n  sorry -- FAKE_SORRY")
            block = r.split("[[LEAK_GOALS]]")[1]
            self.assertIn("[truncated:", block)
            self.assertLess(len(block), 200)
        finally:
            server.BLOCK_MAX_CHARS = old

    async def test_a_wait_that_ends_between_a_messages_header_and_its_body_does_not_desynchronise_the_stream(self):
        """The decisive case: the goal ceiling passes after the answer's header is read and before its body arrives. The old
        wait cancelled the read there, the header was gone, and the body was parsed as the next message's headers; from then on
        every verify failed. The read now stays in flight and the next wait receives the message whole."""
        old = server.GOAL_QUERY_TIMEOUT
        server.GOAL_QUERY_TIMEOUT = 0.4
        try:
            r = await self.d.verify_script("theorem t : True := by\n  sorry -- FAKE_SORRY FAKE_GOAL_SLOW_BODY")
            self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
            self.assertNotIn("[[LEAK_GOALS]]", r)
            r = await asyncio.wait_for(self.d.verify_script("theorem t2 : True := trivial"), 20)
            self.assertTrue(r.startswith(SUCCESS), r)
            r = await asyncio.wait_for(self.d.verify_script("theorem t3 (n : Nat) : n + 0 = n := by\n  sorry -- FAKE_SORRY"), 20)
            self.assertIn("Goal @ line 4 (sorry):", r, r)
        finally:
            server.GOAL_QUERY_TIMEOUT = old

    async def test_a_wait_that_times_out_does_not_lose_the_message_in_flight(self):
        """The read on the LSP stream is not cancelled when a wait times out: a message that arrives just after the wait ended is
        handed to the next wait whole (a cancelled half-read would have desynchronised every later read)."""
        old = server.GOAL_QUERY_TIMEOUT
        server.GOAL_QUERY_TIMEOUT = 0.3
        try:
            for _ in range(3):
                r = await self.d.verify_script("theorem t : True := by\n  sorry -- FAKE_SORRY FAKE_GOAL_STALL")
                self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
            r = await self.d.verify_script("theorem t (n : Nat) : n + 0 = n := by\n  sorry -- FAKE_SORRY")
            self.assertIn("Goal @ line 4 (sorry):", r, "the stream still parses after three abandoned waits")
            r = await self.d.verify_script("theorem t2 : True := trivial")
            self.assertTrue(r.startswith(SUCCESS), r)
        finally:
            server.GOAL_QUERY_TIMEOUT = old

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
        self.assertIn("loaded before it runs", r)
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


class ColdStartCase(_Base):
    """The mechanism behind the 2026-10-20 stalls. A fresh Lean worker needs minutes to load the tree (here 3 s against a 1.5 s
    cap); charged to a script it looked like a timeout, and the next request restarted the load, so it never finished."""

    cold_s = "3"
    warmup_s = 30.0

    async def test_a_cold_start_is_not_charged_to_the_script(self):
        t0 = time.time()
        r = await self.d.verify_script("theorem t : True := trivial", timeout=1.5)
        self.assertTrue(r.startswith(SUCCESS), r)
        self.assertGreater(time.time() - t0, 2.5, "the load took its time")
        self.assertEqual(self.d.verify_timeouts, 0, "and was not a timeout")
        self.assertTrue(self.d._warm)

    async def test_requests_arriving_during_the_load_do_not_restart_it(self):
        rs = await asyncio.gather(*[self.d.verify_script(f"theorem t{i} : True := trivial", timeout=1.5) for i in range(4)])
        for r in rs:
            self.assertTrue(r.startswith(SUCCESS), r)
        self.assertEqual(self.d.verify_timeouts, 0)
        opens = [e["method"] for e in lake_log() if e["method"] in ("textDocument/didOpen", "textDocument/didChange")]
        self.assertEqual(opens.count("textDocument/didOpen"), 1, "one worker, loaded once")

    async def test_after_a_kill_the_replacement_is_warmed_before_the_next_script_so_there_is_no_kill_loop(self):
        await self.d.verify_script("theorem warm : True := trivial", timeout=10)
        r = await self.d.verify_script("theorem big : True := by\n  decide +kernel -- FAKE_STUCK", timeout=1.5)
        self.assertIn("verify exceeded", r)
        self.assertEqual(self.d.worker_restarts, 1)
        self.assertFalse(self.d._warm, "a replaced worker is cold")
        t0 = time.time()
        r2 = await self.d.verify_script("theorem small : True := trivial", timeout=1.5)
        self.assertTrue(r2.startswith(SUCCESS), r2)
        self.assertGreater(time.time() - t0, 2.5, "it waited for the reload, without being charged for it")
        self.assertEqual(self.d.worker_restarts, 1, "no second kill")
        self.assertEqual(self.d.verify_timeouts, 1)

    async def test_health_says_whether_the_worker_is_warm(self):
        from starlette.testclient import TestClient
        server.fast_compiler = self.d
        with TestClient(server.build_app()) as c:
            self.assertFalse(c.get("/health").json()["warm"])
            await self.d.verify_script("theorem t : True := trivial", timeout=10)
            self.assertTrue(c.get("/health").json()["warm"])


class ColdStartThatNeverEndsCase(_Base):
    cold_s = "60"
    warmup_s = 2.0

    async def test_a_tree_that_will_not_load_is_reported_as_loading_and_the_script_is_not_run(self):
        t0 = time.time()
        r = await self.d.verify_script("theorem t : True := trivial", timeout=1.5)
        self.assertIn("still loading the Tengoku tree", r)
        self.assertIn("Nothing was checked", r)
        self.assertLess(time.time() - t0, 12)
        sent = [e for e in lake_log() if e["method"] in ("textDocument/didOpen", "textDocument/didChange")]
        self.assertTrue(all("theorem t : True" not in e["text"] for e in sent), "the user's script never reached a cold worker")


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

    def test_the_statement_form_gate_rejects_the_answer_slot_with_a_message_that_says_why_and_cites_sources(self):
        gate = server.STATEMENT_GATE
        # it looks only at what THIS script declared (nothing in the tree can trip it), at theorems and definitions, through leading
        # binders and through definitions the script made, for an iff whose left side is a bare True, False or sorry
        self.assertIn("env.constants.map₂", gate)
        self.assertNotIn("env.constants.toList", gate, "all constants would include the whole tree")
        for needle in (".thmInfo", ".defnInfo", "getForallBody", ".iff?", "``True", "``False", "``sorryAx", "unfold1", ".defnInfo"):
            self.assertIn(needle, gate)
        # it rejects by throwing, like the axiom gate, so the existing failure path carries it
        self.assertIn("throwError", gate)
        self.assertIn("statement form repudiated", gate)
        # the message names the form, says why in one sentence, says what to write instead, and cites two primary sources
        flat = " ".join(gate.split())
        for needle in ("(True : Prop) <-> P", "filled with the hypothesis itself", "Iff.rfl", "theorem NAME : P", "theorem NAME_neg", "prove whichever holds"):
            self.assertIn(needle, flat)
        self.assertEqual(len(server.STATEMENT_GATE_SOURCES), 2)
        for url in server.STATEMENT_GATE_SOURCES:
            self.assertTrue(url.startswith("https://"), url)
            self.assertIn(url, flat, "the message must carry the link")
        self.assertIn("comparator#definition-holes", server.STATEMENT_GATE_SOURCES[0])
        self.assertIn("formal-conjectures", server.STATEMENT_GATE_SOURCES[1])

    def test_warmup_has_its_own_long_ceiling_above_the_verify_cap(self):
        self.assertGreaterEqual(server.WARMUP_TIMEOUT, 600)
        self.assertGreater(server.WARMUP_TIMEOUT, 2 * server.VERIFY_TIMEOUT, "a cold load (about 200 s) must not be charged to the verify cap")
        self.assertIn("LEAK_WARMUP_TIMEOUT", open(os.path.join(ROOT, "server.py")).read())

    def test_the_tree_import_is_injected_by_default(self):
        self.assertTrue(server.TENGOKU_IMPORTS.startswith("import Tengoku"))

    def test_the_app_serves_refresh_and_health(self):
        app = server.build_app()
        paths = {getattr(r, "path", None) for r in app.routes}
        self.assertIn("/refresh", paths)
        self.assertIn("/health", paths)


if __name__ == "__main__":
    unittest.main()
