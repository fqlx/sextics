# Symmetric sextic research checkpoint

This is a **research checkpoint**, not a solve submission. `Submission.relative_primitive_exists` still has `sorry`, and the protected certificate has not passed its axiom audit. The checkpoint branch is separate because the draft proposal already has 64 changed files and its policy does not permit research scripts or nested directories.

## What is here

- `jet/` contains explicit rational first and second relative deformation jets about a monomial-cubic Fermat fiber, the exact source data, and independent characteristic-zero replay scripts. Put z=λ², K=2(1+c⁶), ell=2(1+z³), q=1+2b−u and r=c²+2cd−zu. The family is F(t)=F0+tH with F0=b⁶+d⁶+K+ell u³ and H=6u+6u²+6zc⁴u+6z²c²u²+(q²r+2qr²)/7. The protected sextic is F(5); the stored identities hold through order t² at t=0, not at t=5.
- The final replay also checks the eight-sector first-order source construction for the alternative symmetry-preserving diagonal family. Its finite trace and binding to the protected Lean theorem remain to be formalized.
- `trace/` preserves the exact raw73 source circuits, a generic damped-resultant trace formulation, and independently checked Cauchy/first-integral identities. None evaluates the required full trace.
- `lean/` snapshots the separately audited, conditional complete-incidence finite-algebra trace backbone and its three scratch dependencies. It constructs total trace and compatible derivations and gives an endpoint assuming an actual current equation and source-trace equality. It does not prove those assumptions. The files retain their scratch module names and are not integrated into the 64-file proposal.

## Replay the algebra checks

With Python 3 and the listed pinned dependencies:

```sh
python3 -m venv .venv
.venv/bin/pip install -r research/symmetric-sextic-residual/jet/requirements.txt
.venv/bin/python research/symmetric-sextic-residual/jet/replay.py
.venv/bin/python research/symmetric-sextic-residual/trace/replay.py
```

The scripts check the target/family relation, the mixed first current, first and second transport, all 22 second-order radial terms and 35 residual currents, and the alternative generic-diagonal first-source construction. They use exact arithmetic; these computer-algebra checks are not Lean kernel proofs. Replaying `lean/` requires the proposal's temporary `Proposal` module layout and the pinned trusted Lean environment; source hashes and the scope of earlier sandbox/kernel checks are in `lean/audit-summary.json`.

The previously suggested 108-curve construction was withdrawn: its polynomial identity omitted a term. It is not used in this checkpoint.
