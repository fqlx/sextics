# Forced source-root moment and residue-preserving fold reduction

Status: an exact constructive partial-current formula, with finite-field
principal checks and a generic rational definition. No complete remainder
cancellation or certificate is claimed.

Use the source-bearing rational coordinates of
`RATIONAL-THREE-ADJOINTS.md`, with w=z², T=1+w³ and

```
N=9i²w²−16JT,
M=256T⁵N+729i⁶Jw⁶,
P=9i²vM−64JwT²N,
v=e⁶=64JwT²N/(9i²M).
```

The actual scalar density satisfies

```
hsrc=−3456i³v w²T³/P_w
    =−288i³v (T⁴)_w/P_w,
H=e^(−5)hsrc.
```

The true source forcing is Rsrc=(D−6)(D−5)hsrc. Every full-kernel and
Cartan term remains as in the audited three-box reconstruction.

## Principal equation dictated by the actual source

All P derivatives below hold i,J,v independent. Define

```
Kz=vP_v,
KD=6vP_v−2iP_i−2JP_J,
K1=vP_v+JP_J,
K3=4vP_v−iP_i−JP_J,
sigma3=P_i³+v K1 Kz K3,
Nsrc=−3456i³v w²T³.
```

At a generic simple fold P=P_w=0, hsrc has order-one pole in a local
ramification coordinate. The order-five principal coefficients are

```
Rsrc:                  +3 Nsrc P_ww² KD²/P_w⁵,
mathcalP3 G(i,J,w):     −3 G_w P_ww² sigma3/P_w⁵.
```

Thus the derivative of a regular inverse-root moment is forced by

```
G_w sigma3=−Nsrc KD² modulo (P,P_w).                    (1)
```

Let C(i,J,w) be the monic, saturated, squarefree critical polynomial,
obtained by substituting v=v(w) into P_w and removing fixed v=0 and
v=infinity factors. It has degree24. Work over K=Q(i,J).
Reduce the rational functions in (1) modulo C; all fixed denominators
are inverted only where coprime to C. The multiplication matrix of
sigma3 in K[w]/C is generically invertible. A valid exact finite-field
specialization with nonzero determinant proves that its determinant is
not the zero rational function, and therefore defines a generic rational
inverse. Write

```
r=rem_C[−Nsrc KD²/sigma3], degree_w(r)<24.
```

The unconstrained moment G0=integral r dw has degree≤24. This is a
forced algebraic construction, not a polynomial search ansatz.

## Preserving the already served finite-N residue

An unconstrained G0 can change the N-residue. To preserve it, put

```
Qfixed=N²,
Hcrt=rem_C[r/(Qfixed C_w)],
G_N=Qfixed C Hcrt.                                    (2)
```

Because C is squarefree and generically coprime to N, all inverses in
(2) are defined over the same generic rational field after adjoining
their explicit resultant denominator. Directly,

```
N² divides G_N,
(G_N)_w=r modulo C.
```

Thus (2) still matches the actual source principal equation (1).
Its forced degree is≤53, distinct from the unconstrained degree≤24.
No expansion of its rational coefficients is needed to define it:
the two quotient inverses are finite24×24 matrix adjugate/determinant
expressions, which can be evaluated and differentiated exactly.

At a generic N=0 branch, v has a simple zero and N is v times a unit.
Consequently G_N=O(v²). The operators A=partial_i|v and
B=partial_J|v preserve the ideal(v²), and Z=v partial_v preserves it.
Therefore the full rationalized cubic output mathcalP3(G_N)=O(v²).
Its normalized potential is e^(−1)G_N=O(e¹¹), and its normalized
output is e^(−7)mathcalP3(G_N)=O(e⁵). Its Green derivatives and Cartan
fiber terms remain regular at this boundary. This verifies preservation
with the actual e rescalings, not merely with the unscaled scalar G.
In particular it creates no coefficient of v¹ in the retained
`dv/v²` residue calculation.

Only the finite-N residue is served by (2). The infinity, fixed-root
and other (Z−1) remainders must remain explicit. Further CRT factors
or finite jet conditions may be imposed when needed, provided they
remain coprime to C.

## Compatibility with the actual residue lift

If the source's N residues are first served by the coupled Ore/CRT
potentials, apply the construction to the **remaining** order-five
principal coefficient, not to Nsrc KD² alone. For a quadratic potential
F=N_F/P_w, its contribution at that order is

```
mathcalP1(F): +3N_F P_ww² sigma1/P_w⁵,
sigma1=KD²+P_i K3;
mathcalP2(F): +3N_F P_ww² sigma2/P_w⁵,
sigma2=4J P_J²+P_i K1.
```

A preexisting regular cubic potential contributes the sigma3 term above.
Subtract all these actual terms before computing the new r in (1).
Formula (2) then preserves the served finite-N residue.

## Lower folds and the remaining source

The difference after the full cubic current is an explicit rational
function Rrem=Rsrc−mathcalP3(G_N), or the corresponding difference after
the residue lift. No unknown terms are silently discarded.
At simple folds the trace of a regular inverse-root moment and of the
source residue moment is analytic; the negative ramification Laurent
terms have odd orders. Matching the order-five term therefore lowers
the possible fold pole to order3. The quadratic regular moments have
principal order-three symbols sigma1 and sigma2. These symbols are
also generically invertible modulo C, as witnessed independently at
the exact finite-field points below. The same finite quotient/CRT
construction can match the lower fold while preserving N².
The final regular/(Z−1) remainder is not asserted to vanish.

`match_source_root_principal.py` checks the source-specific congruence,
the CRT derivative congruence and N² divisibility at three exact
mod1009 points (i,J)=(1,1),(2,3),(5,7). Every point has critical degree24,
gcd(C,sigma3)=gcd(C,sigma1)=gcd(C,sigma2)=1, and a degree53 CRT moment.
Root's independent `verify_fold_symbol_witness.py` checks a separate
valid specialization and the generic critical-polynomial construction.
