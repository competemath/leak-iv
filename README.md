---
title: Leak IV
emoji: 👀
colorFrom: red
colorTo: green
sdk: docker
pinned: false
short_description: Leak IV
---

Check out the configuration reference at https://huggingface.co/docs/hub/spaces-config-reference

## Goals at every hole, and the compiler's own messages

A `sorry` is a warning and so a failure, but the warning names the declaration, not the hole: a prover that scaffolded a proof with
`sorry`s got nothing back but "declaration uses sorry" (the LRR Control II transcripts, 2026-08: a median 6.5 such warnings per unsolved
problem, every one empty). A failed compile now also carries, after the diagnostics:

- `[[LEAK_GOALS]]` — for every `sorry` in the script, the hypotheses and the goal at that point (`$/lean/plainGoal`, or
  `$/lean/plainTermGoal` for a term-mode sorry), one entry per hole, numbered like the diagnostics; and every `unsolved goals` /
  unfilled `?_` error repeated with its line breaks (the diagnostic line itself stays on one line, as callers parse it).
- `[[LEAK_INFO]]` — every severity-3 message that is not a tactic suggestion: `#eval`, `#check`, `trace_state`, `#print` output
  (on a success too). Suggestions (`exact?`, `apply?`) stay under `[[LEAK_SUGGESTIONS]]`, which comes last.

Neither block touches the verdict, the `Line N (Error|Warning):` grammar or the certificate; both are capped (`LEAK_BLOCK_MAX_CHARS`,
24 000) and every line of them is prefixed `  | `, with the verdict phrases and `[[` disarmed, so nothing a script prints can imitate a
diagnostic, a suggestion or a success. The goal queries share one ceiling (`LEAK_GOAL_TIMEOUT`, 20 s; at most `LEAK_GOAL_MAX_SORRIES`,
24, holes): past it the answer goes out with the goals it has, and the verdict never waits on a goal. `tests/test_lean_lsp.py` runs
all of it against the toolchain's real language server (CI: the tree's toolchain and the next release).

## Statement-form gate: no answer slots

A theorem whose statement is an `↔` with a bare `True`, `False` or `sorry` on its left (`(True : Prop) ↔ P`, `(False : Prop) ↔ P`,
`(sorry : Prop) ↔ P`) is rejected with an error that says why and links to two sources. A free Prop slot has to be policed from outside
the kernel: it can be filled with the hypothesis itself and closed by `Iff.rfl`, so a proof of it need not settle the question. The
comparator's documentation says such definition holes "can be gamed" and must always get an additional check
(<https://github.com/leanprover/comparator#definition-holes>), and formal-conjectures dropped `answer(sorry)` for the plain statement,
negated with `¬` when the answer is no (<https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md#the-question-attribute>).
State a question as two plain theorems (`theorem NAME : P`, and separately `theorem NAME_neg : ¬ (P)`) and prove whichever holds.

The gate only looks at declarations the script itself added, looks through definitions the script made and through leading binders, and
is compiled after the axiom-closure gate and left out of the saved certificate. `tests/test_lean_gates.py` runs both gates in real
Lean (CI: the tree's toolchain and the next release).
