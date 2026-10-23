# Generic cyclic scalar route: exact boundary obstruction

The generic rational charged scalar equation has no solution over
`C(eta,V,s)`, and hence none over a finite algebraic extension of that same
field. This is a limitation of this sufficient scalar reduction. It does
not exclude a special-invariant-level solution or a general legal sextic
certificate outside the reduction.

The proof is [resonance_obstruction.md](resonance_obstruction.md). It first
audits the actual B=0 ramification and charge, then takes the invariant
`s=0` boundary and `nu=9eta+14=0` inside it. The resulting exact rational
ODE is `T4^2 f=R0`. Rational-function valuation bounds require
`V^5 f` to have degree at most ten and be divisible by `(1+V^6)^2`, of
degree twelve, a contradiction.

Reproduce the independent exact derivations with:

```
python audit_components.py
python resonance_obstruction.py
python independent_contracted_audit.py
```

`audit_components.py` proves the compact pullback
`B=243c^2 eta^6 s^2 k^2/q^2` and distinguishes its three generic affine
components. `resonance_obstruction.py` derives the two boundary operators
directly from the pinned physical vector field, raw charge numerator and
source. The independent parent replay in
`independent_contracted_audit.json` instead starts from `Bred/Cred/rhsred`,
bypasses the compact charge formulas, and checks all formal-jet coefficients.
All its checks passed.

The two `leading_*` finite-prime searches are earlier diagnostics, not proof
inputs. No certificate, Lean verification, external post, or protected
repository edit was made.
