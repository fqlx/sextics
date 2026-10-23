# One source-derived normal-R candidate with its actual residual

This records a constructive partial current, not a solution. No coefficient
grid, pole-order screen, or nonexistence argument is used.

Use the complete scalar closure notation. Let

    R=−27C^3/a+(81/4)Cz^2a−(27/16)z^3a^2,
    Delta=4C^6−729H^4,
    g=R/C^3,
    f=C^2 Delta g=Delta R/C.

This shift comes directly from the three normal-R terms: if theta0 is the
formal derivative C partial_C with a,z held fixed, the exponents in g are
0,−2,−3. Consequently

    theta0(theta0−1)(theta0+2)(theta0+3)g=0.

The remaining formal Euler polynomial gives

    C^4(theta0+4)^2(2theta0−1)(2theta0+5)g
      =2160 C^4/a−405C^2z^2a−(189/16)Cz^3a^2.

These statements use theta0 only. They do not replace the actual physical
D_C, which moves a and produces nonzero additional terms.

## Actual leading ramification correction

Write J=P_a, K=P_aa, M=P_C and

    N=a^2−(2C/(3H))P_C,
    T(a)=N/J.

At a generic smooth ramification point J=0, with M,K,N nonzero, the actual
physical scalar operator has the leading Laurent term

    L* f=−15 M^4 K^3 f_a/J^7+lower pole order.

Here f_a holds H,C,z fixed. An explicit horizontal current cancelling this
leading term in −L*f+T U is

    U0=3 M^4 K^2 f_a/(N J^5),   W0=0.

Indeed,

    T(U0)=−15 M^4 K^3 f_a/J^7+lower pole order.

For a split correction U=u/J^5, W=w/J^5, the leading condition is

    N u−P_z w=3M^4K^2 f_a.

The displayed U0 introduces N poles. Those poles and all lower ramification
terms remain obligations; the leading cancellation is not a global solve.

## Exact complete remaining source

The completely specified rational scalar residual for this partial current
is

    E=phi_H/6 + L*(Delta R/C)
        −T[3P_C^4 P_aa^2 partial_a(Delta R/C)/(N P_a^5)].

All operators here are the actual physical derivations from
`SCALAR-HORIZONTAL-CLOSURE.md`. This expression includes every compact
component through the explicit scalar-to-rank-four reconstruction.

`normal_R_candidate.py` evaluates this exact expression with standard-library
Fraction jets. It computes a(C) by implicit Newton in the truncated jet ring,
so all first through fourth physical a derivatives are retained. The H,z
values are fixed along that jet; the T jet uses both T(C)=2C/(3H) and
T(a)=N/P_a. At

    a=C=z=1, H=969/64,

E is nonzero. Its exact value and the separate sigma,L*f,TU terms are saved
in `normal-R-candidate-results.json`. This is a single candidate residual
calculation. It neither excludes other f,U,W nor closes this source-driven
candidate's further horizontal correction.

`verify_normal_R_critical_jet.py` checks the leading cancellation in the
principal Laurent grading. At smooth ramification,

    D_C(P_a)=−P_C P_aa/P_a+O(1),
    T(P_a)=N P_aa/P_a+O(1).

The exact principal coefficient recurrence is
`ell_1=−P_C f_a`, `ell_(n+1)=(2n−1)P_C P_aa ell_n`.
It gives the displayed fourth-derivative coefficient. The smooth hypotheses
are bound to the actual rational point `(a,H,C,z)=(1,3,1/3,0)`, where both
`L*f` and `T(U0)` have the same nonzero principal coefficient
`142818675793920`. Their contributions in `−L*f+T(U0)` cancel exactly.
