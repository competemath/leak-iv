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
