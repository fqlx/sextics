# Actual compressed pair leaving the simple R0 source

This is an explicit rational pair with its complete nonzero-or-zero residue
obligation retained. It is not a complete solution. All bare C derivatives,
the fourth-order adjoint, and every auxiliary denominator remain.

Use the source-guided Euclidean currents U0,W0 from
`SOURCE-HORIZONTAL-BEZOUT.md`, and put

    R=R0(a,z), D0=partial_a U0+partial_z W0,
    Dnum=R^2 D0,
    Y=H_z partial_a−H_a partial_z,
    A=Y(R), B=delta(A), delta=partial_C|a,z.

The expression Dnum has no R denominator. Also delta(R)=0 exactly. Define

    g2=A^4 Dnum/(24 B^4),
    s1=[Dnum−Lhat_delta*(g2)]/A,
    G2=g2/R^2,
    S1=s1/R.

Then the exact complete rational identity is

    Lhat_delta*(G2)−Y(S1)=D0−Y(s1)/R.

Indeed delta(R)=0 permits the whole adjoint to pass through R^−2, while

    Y(s1/R)=Y(s1)/R−s1 A/R^2.

The actual unmatched simple source is therefore

    F_simple=Y(s1),
    residual=−F_simple/R.

No part of F_simple is omitted or fitted: Lhat_delta* includes the actual
physical bare-C derivatives through order four. In particular all four
compact components enter through the previously verified scalar closure.

## Why the apparent A denominator cancels on its regular open

Where B and all scalar-operator coefficients are regular units, g2 is A^4
 times a regular coefficient. Consequently every term of derivative order
at most three is divisible by A. The fourth derivative gives

    delta^4(A^4)=24B^4 mod A,
    Lhat_delta*(g2)=Dnum mod A.

This includes derivatives of B^−4 and of Dnum: they multiply a remaining A
factor at derivative order four. Thus the numerator defining s1 is divisible
by A on this regular open. This does not remove B, N, H, Delta, or other
auxiliary poles, nor their intersections.

## An actual smooth divisor point for residue evaluation

Factoring vertical slices of the displayed exact R0 found the point

    prime=1009, (a,z,C)=(5,564,1).

The exact finite-field values are

    R0=0,
    partial_a R0=722, partial_z R0=978,
    A=Y(R0)=274, B=delta A=637,
    H=980, N=794, Delta=236.

Thus R0 is smooth there and A,B,H,N,Delta are units. The parent evaluated the actual nested Taylor jets, including every bare-C
derivative of the monic adjoint and the parameter derivatives in Y. The exact
result is

    Dnum=525, g2=972, s1=511, F_simple=Y(s1)=372 mod 1009.

Thus this explicit pair has a nonzero unmatched simple R0 source. Its complete
source remains `−Y(s1)/R0`; no term has been dropped. The parent computation
and constants are saved in `../evaluate_R0_residue.py` and
`../R0-simple-residue-results.json`.

This is a failure of the displayed partial pair, not an intrinsic obstruction.
The R0 poles themselves are auxiliary: where H_a is a unit, the exact free
choice S_a=W0/H_a replaces the flux current by `(−rho/(6H_a),0)` and removes
R0 while introducing H_a poles. In particular the original regular-source
class remains untouched by that pole trade. The parent checked the baseline
with exactly the same mixed jets: setting g2=0 gives

    s1_base=Dnum/A=720, Y(s1_base)=0 mod 1009.

Thus the value372 belongs to the displayed nonzero-G2 partial pair; it is
not an intrinsic residue obstruction. Every B,N,H,Delta,H_a or other
auxiliary pole and every compact component remains an obligation.

`verify_compressed_pair.py` checks the exact compressed-pair identity and
the complete principal-A interpolation. `find_R0_point.py` generates the
physical R0 and the saved point values in `R0-point.json`. Finding a divisor
point is not a degree-family or denominator search, and supplies no
nonexistence conclusion.
