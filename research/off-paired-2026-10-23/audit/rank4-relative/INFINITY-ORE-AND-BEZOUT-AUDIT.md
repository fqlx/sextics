# Exact checks of two constructive source mechanisms

The separate SymPy implementation `verify_infinity_ore_independent.py`
checks the full noncommutative identity `U L+V M=1`, its formal adjoint,
adjoint involutions, the actual scalar T-commutation of V*, and three
Laurent-source applications. All 13 exact groups pass. It rebuilds operator
composition and formal adjunction rather than importing the primary checker.
The M coefficients are taken from the stored, previously audited infinity
compact projection; this check does not rederive the fiber reduction.

The standard-library implementation `verify_source_bezout_fraction.py`
checks the actual physical H derivatives, the quadratic Euclidean identities,
and `H_a U0+H_z W0=-q^3/(6a^2)` at ten distinct rational physical points.
All ten exact groups pass. These substitutions supplement the primary generic
polynomial-identity proof in `verify_source_bezout.py`; they are not a generic
proof by sampling.

Neither check supplies a rational solution of the remaining forced equation.
The infinity source match still requires cancellation of its residue. The
horizontal Bezout current still requires G and its free Hamiltonian S.
No certificate or Lean verification is claimed.
