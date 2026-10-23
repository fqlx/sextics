# Off-paired: source-bound elliptic calculations

This is local research on the unchanged `off-paired` instance at sextics
commit `cb551854693127a2542fb405f7ceb47ae0b35a09`. No solution has been obtained.
No files here constitute a checked Lean certificate or a proof of unrestricted
nonexistence. Nothing has been posted externally.

The main positive result in this round is an exact reduction of the actual
source, rather than a surrogate deformation, to a rank-two elliptic
Gauss--Manin equation. The physical double cover is retained throughout.

## Exact reduction

Set `r=h^2-4`, `J=1+q^6`. The scaled Weierstrass equation is
`y^2=x^3+A*x+B`, with

```
A = (3/2)*J*h*r^2*k - h*q^5/32 - r^2/3888
B = h*r^3*(q^3/8-27*J^2*h/4)*k^2
    +h*r^2*(q^4/48+5*J*r/216)*k
    -J*h^2*q^6/64+h*q^5*r/3456+r^3/629856
A_lambda = q^2*h^2*(36*r*k-q)/48
B_lambda = q^2*h^2*r*(108*r*k+2916*J*q*h*k+q)/5184
Delta = 4*A^3+27*B^2.
```

The remaining physical cover is `W^2=k^2-4`. The scaling absorbed the
former `sqrt(h^2-4)` factor in the holomorphic density. For the column
basis `(dx/y,x*dx/y)`, write

```
C_i = 2*A^2*A_i+9*B*B_i
E_i = 3*B*A_i-2*A*B_i
G_i = [[-C_i,A*E_i],[3*E_i,C_i]]/(2*Delta).
```

A rational solution of

```
sum_i (partial_i+G_i-delta_(i,k)*k/(k^2-4))*H_i
    = -G_lambda*(1,0)^T,       i=k,q,h,
```

is a sufficient construction of a primitive, after restoring the explicitly
known Hermite, moving-map and normal-chart corrections. It is not a necessary
condition on every possible divisor support.

`gm/manual_gauge.md`, `gm/gauge_fisher.py`, and
`gm/verify_raw_module.log` record an independent exact gauge from the raw
affine cubic module. All 16 polynomial module identities, the three tangent
directions and the actual lambda source passed exact verification. The
normalization audits are in `normalization_audit/`. The original polynomial
packet is `../round6/k3_normalform/lambda_gm.pickle`.

## Rational-current searches

`pde/search.py` builds exact rational coefficient columns for bounded
denominators and numerator spaces, then screens them over a good prime.
`pde/primitive_log_search.py` adds seven primitive logarithmic vector fields
along `Delta=0`. The bounds and saved matrices are essential to interpretation.
Two searches are in `pde/box_1_8_6/` and `pde/box_2_10_8/`.
The latter has 2,970 columns and 7,492 rows and has a verified modular left
witness. This alone is a modular exclusion; no unrestricted or automatic
characteristic-zero exclusion is asserted from that witness.

Other bounded searches and their separate rank qualifications are recorded
in `pde_fresh/`, `off_paired_pde/`, and `certificate_audit/`.
No positive rational solution has been found. In particular, failures on a
chosen denominator do not exclude other supports or higher numerator spaces.

The full logarithmic module is larger than the original seven-field ansatz.
`certificate_audit/log_derivation/` supplies exact QQ lifts of additional
syzygies of `(Delta_k,Delta_q,Delta_h,Delta)`. `pde/full_log_search.py`
independently rechecks those identities and their connection divisibility.
The new search `pde/full_log_box_20_1_10_6/` contains 17 such fields plus
the original seven and regular fields: 4,158 columns, 6,100 rows, and a
verified modular left witness. Its scope file records which exact fields
were actually available; the number 20 is an index bound, not a count.

## Constructive divisor families

For a moving line `x=s*k+t`, put

```
C(k) = s^3*k^3+c2*k^2+c1*k+c0
c2 = 3*s^2*t+a1*s+b2
c1 = 3*s*t^2+a1*t+a0*s+b1
c0 = t^3+a0*t+b0,
```

where `A=a1*k+a0`, `B=b2*k^2+b1*k+b0`. The physically odd genus-two
factor is `Z^2=(k^2-4)*C(k)`.

The Chebyshev conditions `c2=0`, `c1=-3*s^3` give
`Z^2=s^3*(k^2-4)*(k^3-3*k-tau)`. It has the exact elliptic map

```
X = k^3-3*k,     Y = (k^2-1)*Z
Y^2 = s^3*(X^2-4)*(X-tau),     dX/Y = 3*dk/Z.
```

Thus this map captures the correct odd differential. The global holomorphic
two-form and nonzero source Gysin image still require proof. The second
elliptic quotient and the full physical incidence formulas are in
`off_paired_pde/moving_line/`. A separate fixed-j1728 incidence construction
is in `moving_j1728/`; its source image is likewise unproved.

The isotrivial supports `A=0` and `B=0` have significant boundary geometry;
normal-cover irregularity calculations do not automatically survive resolution.
The selected mixed holomorphic-two-form routes are now excluded after exact
global audits. For `A=0`, the two canonical character ideals impose 4 and 56
independent conditions and have vanishing H1; see
`isotrivial_A/character_finish.md`. For `B=0`, the required character on the
genus-87 normalized fiber has an injective exact QQ Rauch/KS pairing of
rank 14; see `isotrivial_B/rauch_KS_exact.*` and the independent audit
`independent_audits/rauch_B.md`. The earlier raw Cayley Jacobian rank was
insufficient because it detected node torsion; the normalization correction
is essential. Pure base-pulled forms have zero Gysin image by projection.

`normalization_audit/delta_support_audit.md` records other support-image
calculations, including horizontal discriminant fibers and J=0. It preserves
the unresolved compact source-binding qualification: dense-open lambda
identities alone do not establish a simultaneous smooth proper family or a
nonzero compact transcendental projection. Consequently this note does not
assert an unrestricted impossibility theorem for the entire GM ansatz.

The algebraic Kuga--Satake and primitive-lattice results from round6 remain
useful fiberwise data. They do not, by themselves, give coniveau one for the
actual class on the total fourfold.
