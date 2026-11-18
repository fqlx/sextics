# Cycle Q2 proof checkpoint

The parent commit is the checked head of [draft PR #245](https://github.com/hodge-computer/sextics/pull/245). Its 803 compilation units passed locally. The protected theorem still depends on the admitted affine residue exactness statement.

This branch preserves the in-progress Lean sources from the PR worktree in their original paths under `data/cycle-q2/`, together with two further source dependencies. The combined draft tree has not passed an end-to-end build. The separate `formal-drafts/Proposal/` tree contains work on the full residue, its normal coefficient, and descent, using the temporary `Proposal` import layout.

The `calculations/` directory contains exact arithmetic scripts, derivations and individual replay results for the genus-ten Euler correction, two scalar reductions, the Fermat Higgs matrices, and candidate pole divisors. Each result has the scope described in its own notes. A rational primitive for the original four-form remains open.

Prepared for fqlx with OpenAI ChatGPT and Codex assistance. The mathematical credits and prior work are recorded in the proposal explanation and in the calculation notes.

All local `Proposal` imports referenced by these saved drafts have source files in this branch. The mathlib and shared project dependencies use the repository’s pinned versions.
