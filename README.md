# tombstones

Append-only. `branches.jsonl` has one line per branch that was deleted from this repository: its name, the commit it pointed at, why deleting it lost nothing (`A` fully on the default branch, `B` head of a merged PR, `C1` head of a closed PR, kept at `refs/pull/N/head`) and the command that brings it back. Never edit or remove a line; a restored branch gets a new line.
