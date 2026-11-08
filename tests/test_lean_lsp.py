"""The daemon against REAL Lean's language server, not the fake: the goal at a `sorry` ($/lean/plainGoal), the term goal of a
term-mode `sorry` ($/lean/plainTermGoal), `#eval` output as info, and an `unsolved goals` error repeated with its line breaks. Core
Lean only (`import Lean`, no Mathlib, no tree): a `lake` shim on the PATH runs `lean --server`, which speaks the same protocol as
`lake serve`. These run when `lean` is on the PATH (the `lean-gates` CI job installs it, for the toolchain the tree is on and for the
next release) and are skipped otherwise; LEAK_REQUIRE_LEAN=1 makes a missing `lean` a failure.

    LEAK_LEAN_TOOLCHAIN=leanprover/lean4:v4.34.0-rc2 python -m unittest tests.test_lean_lsp -v
"""
import asyncio
import os
import shutil
import stat
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = shutil.which("lean")
TOOLCHAIN = os.environ.get("LEAK_LEAN_TOOLCHAIN", "").strip()

_DIR = tempfile.mkdtemp(prefix="leak-lsp-")
_BIN = os.path.join(_DIR, "bin")
os.makedirs(_BIN)
_PROJECT = os.path.join(_DIR, "project")
os.makedirs(_PROJECT)
if LEAN:
    shim = os.path.join(_BIN, "lake")
    with open(shim, "w") as f:
        f.write(f'#!/bin/sh\n# `lake serve` -> the toolchain\'s own server\nexec "{LEAN}" {("+" + TOOLCHAIN) if TOOLCHAIN else ""} --server\n')
    os.chmod(shim, os.stat(shim).st_mode | stat.S_IEXEC)
os.environ["PATH"] = _BIN + os.pathsep + os.environ.get("PATH", "")
os.environ["LEAN_PROJECT_PATH"] = _PROJECT
os.environ["TENGOKU_AUTO_REFRESH"] = "0"
sys.path.insert(0, ROOT)
import server  # noqa: E402


@unittest.skipUnless(LEAN or os.environ.get("LEAK_REQUIRE_LEAN"), "no `lean` on the PATH (the lean-gates CI job runs these)")
class RealLspCase(unittest.IsolatedAsyncioTestCase):
    @classmethod
    def setUpClass(cls):
        if not LEAN:
            raise AssertionError("LEAK_REQUIRE_LEAN is set but `lean` is not on the PATH")
        cls._imports = server.TENGOKU_IMPORTS
        server.TENGOKU_IMPORTS = "import Lean"  # the gates need it; there is no tree here

    @classmethod
    def tearDownClass(cls):
        server.TENGOKU_IMPORTS = cls._imports
        shutil.rmtree(_DIR, ignore_errors=True)

    async def asyncSetUp(self):
        self.d = server.LeanCompilerDaemon()
        await self.d.boot()

    async def asyncTearDown(self):
        p = self.d.process
        if p and p.returncode is None:
            p.kill()
            try:
                await asyncio.wait_for(p.wait(), 5)
            except asyncio.TimeoutError:
                pass

    async def test_the_goal_at_a_tactic_sorry(self):
        r = await self.d.verify_script("theorem t (n : Nat) (h : n ≠ 0) : n + 0 = n := by\n  sorry")
        self.assertTrue(r.startswith("❌ Compilation Failed:"), r)
        self.assertRegex(r, r"Line 3 \(Warning\): declaration uses .sorry.")
        self.assertIn("[[LEAK_GOALS]]", r)
        self.assertIn("Goal @ line 4 (sorry):", r)
        self.assertIn("  | n : Nat", r)
        self.assertIn("  | h : n ≠ 0", r)
        self.assertIn("  | ⊢ n + 0 = n", r)

    async def test_two_sorries_two_goals_in_order(self):
        r = await self.d.verify_script("theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  refine ⟨?_, ?_⟩\n  · sorry\n  · sorry")
        g = r.split("[[LEAK_GOALS]]")[1]
        self.assertLess(g.index("Goal @ line 5 (sorry):"), g.index("Goal @ line 6 (sorry):"))
        self.assertIn("  | ⊢ p", g)
        self.assertIn("  | ⊢ q", g)
        self.assertNotIn("  | ⊢ p ∧ q", g, "the goal at each hole, not the theorem")

    async def test_a_term_mode_sorry_has_its_type_as_the_goal(self):
        r = await self.d.verify_script("theorem t : 2 + 2 = 4 := sorry")
        self.assertIn("Goal @ line 3 (sorry):", r)
        self.assertIn("⊢ 2 + 2 = 4", r)

    async def test_unsolved_goals_are_repeated_with_their_line_breaks(self):
        r = await self.d.verify_script("theorem t (a b : Nat) (h : a = b) : b = a := by\n  have h2 : a = b := h\n  done")
        self.assertRegex(r, r"(?m)^Line 5 \(Error\): unsolved goals a b : ℕ h h2 : a = b ⊢ b = a$|^Line 5 \(Error\): unsolved goals a b : Nat h h2 : a = b ⊢ b = a$")
        self.assertRegex(r, r"Goal @ line 5 \(error\):\n  \| unsolved goals\n  \| a b : (ℕ|Nat)\n  \| h h2 : a = b\n  \| ⊢ b = a")

    async def test_eval_output_is_info_and_the_proof_still_verifies(self):
        r = await self.d.verify_script("#eval 6 * 7\ntheorem t : True := trivial")
        self.assertTrue(r.startswith("✅ Compilation Successful!"), r)
        self.assertIn("[[LEAK_INFO]]\nInfo @ line 3:\n  | 42", r, r)

    async def test_a_sorry_in_a_comment_asks_nothing_and_a_clean_proof_passes(self):
        r = await self.d.verify_script("-- sorry\n/- sorry -/\ntheorem t : True := trivial")
        self.assertTrue(r.startswith("✅ Compilation Successful!"), r)
        self.assertNotIn("[[LEAK_GOALS]]", r)
