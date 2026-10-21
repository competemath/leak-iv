"""The two gates compiled by REAL Lean, not by the fake `lake serve` the other tests use: a gate that does not compile, or that
rejects an ordinary proof, would break every verification (the first deployment of the axiom gate did exactly that), and a fake
cannot tell. These run when `lean` is on the PATH (the `lean-gates` CI job installs it, for the toolchain the tree is on and for the
next release) and are skipped otherwise; LEAK_REQUIRE_LEAN=1 makes a missing `lean` a failure.

Each case is a whole file: `import Lean`, the case, then the two gates exactly as server.py sends them."""
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
import server  # noqa: E402

LEAN = shutil.which("lean")
# LEAK_LEAN_TOOLCHAIN=leanprover/lean4:v4.34.0-rc2 picks a toolchain through elan's proxy (`lean +<toolchain>`)
TOOLCHAIN = os.environ.get("LEAK_LEAN_TOOLCHAIN", "").strip()
SLOT_PROOF = "⟨fun _ => rfl, fun _ => trivial⟩"

# (name, source, substring the diagnostics must contain, or None when the file must compile cleanly)
CASES = [
    ("ok_arithmetic", "theorem t (n : Nat) : n + 0 = n := by simp", None),
    ("ok_iff_symm", "theorem t (a b : Prop) (h : a ↔ b) : b ↔ a := h.symm", None),
    ("ok_iff_refl", "theorem t (p : Prop) : p ↔ p := Iff.rfl", None),
    ("ok_true_on_the_right", "theorem t (p : Prop) (h : p) : p ↔ True := ⟨fun _ => trivial, fun _ => h⟩", None),
    ("ok_plain_negation", "theorem t : ¬ (1 = 2) := by decide", None),
    ("ok_plain_statement", "theorem t : ∀ a : Nat, a + 0 = a := by simp", None),
    ("ok_definition_of_a_property", "def Even' (n : Nat) : Prop := n % 2 = 0\ntheorem t : Even' 4 := by unfold Even'; decide", None),
    ("ok_two_plain_statements", "theorem q : 1 + 1 = 2 := rfl\ntheorem q_neg : ¬ (1 + 1 = 3) := by decide", None),
    ("bad_true_slot", f"theorem t : (True : Prop) ↔ (1 = 1) := {SLOT_PROOF}", "statement form repudiated"),
    ("bad_true_slot_unascribed", f"theorem t : True ↔ (1 = 1) := {SLOT_PROOF}", "statement form repudiated"),
    ("bad_false_slot", "theorem t : (False : Prop) ↔ (1 = 2) := ⟨False.elim, fun h => absurd h (by decide)⟩", "statement form repudiated"),
    ("bad_sorry_slot", "theorem t : (sorry : Prop) ↔ (1 = 1) := by sorry", "statement form repudiated"),
    ("bad_slot_under_binders", f"theorem t (n : Nat) (m : Nat) : (True : Prop) ↔ n = n := {SLOT_PROOF}", "statement form repudiated"),
    ("bad_slot_through_a_definition", f"def S : Prop := True\ntheorem t : S ↔ (1 = 1) := {SLOT_PROOF}", "statement form repudiated"),
    ("bad_slot_through_two_definitions", f"def S0 : Prop := True\ndef S1 : Prop := S0\ntheorem t : S1 ↔ (1 = 1) := {SLOT_PROOF}", "statement form repudiated"),
    ("bad_statement_hidden_in_a_definition", f"def Q : Prop := True ↔ (1 = 1)\ntheorem t : Q := {SLOT_PROOF}", "statement form repudiated"),
    ("bad_private_theorem", f"private theorem t : (True : Prop) ↔ (1 = 1) := {SLOT_PROOF}", "statement form repudiated"),
    ("bad_inside_a_namespace", f"namespace Foo\ntheorem t : (True : Prop) ↔ (1 = 1) := {SLOT_PROOF}\nend Foo", "statement form repudiated"),
    ("bad_among_good_ones", f"theorem a : 1 + 1 = 2 := rfl\ntheorem b : (False : Prop) ↔ (1 = 2) := ⟨False.elim, fun h => absurd h (by decide)⟩\ntheorem c : 2 + 2 = 4 := rfl", "statement form repudiated"),
    ("bad_axiom_still_caught", "axiom cheat : False\ntheorem t : 1 = 2 := cheat.elim", "rogue axiom"),
]


@unittest.skipUnless(LEAN or os.environ.get("LEAK_REQUIRE_LEAN"), "no `lean` on the PATH (the lean-gates CI job runs these)")
class RealLeanCase(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not LEAN:
            raise AssertionError("LEAK_REQUIRE_LEAN is set but `lean` is not on the PATH")
        cls.dir = tempfile.mkdtemp(prefix="leak-gates-")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir, ignore_errors=True)

    def compile(self, name, source):
        path = os.path.join(self.dir, name + ".lean")
        text = "import Lean\n\n" + source.strip() + "\n\n" + server.AXIOM_CHECK.strip() + "\n\n" + server.STATEMENT_GATE.strip() + "\n"
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        cmd = [LEAN] + ([f"+{TOOLCHAIN}"] if TOOLCHAIN else []) + [path]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        return p.returncode, (p.stdout + p.stderr)

    def test_cases(self):
        for name, source, expect in CASES:
            with self.subTest(case=name):
                code, out = self.compile(name, source)
                if expect is None:
                    self.assertEqual(code, 0, f"{name} must compile cleanly:\n{out}")
                    self.assertNotIn("error", out.lower(), out)
                else:
                    self.assertNotEqual(code, 0, f"{name} must be rejected:\n{out}")
                    self.assertIn(expect, out)

    def test_the_rejection_carries_both_sources_and_names_the_declaration(self):
        code, out = self.compile("message", f"theorem slotted : (True : Prop) ↔ (1 = 1) := {SLOT_PROOF}")
        flat = " ".join(out.split())
        self.assertNotEqual(code, 0)
        self.assertIn("slotted", flat)
        for url in server.STATEMENT_GATE_SOURCES:
            self.assertIn(url, flat)

    def test_nothing_is_reported_twice_for_a_clean_file(self):
        code, out = self.compile("clean", "theorem t : 2 + 2 = 4 := rfl")
        self.assertEqual((code, out.strip()), (0, ""))


if __name__ == "__main__":
    unittest.main()
