# Complete genus-four compact reduction by one marked point

This constructs a complete rank-eight compact reduction mechanism. It does
not integrate the remaining physical scalar source and is not a certificate.
The finite-field matrices below are exact specialization data, not claimed
to be the universal rational connection matrices.

Work on the smooth generic complete intersection

```
C1=abt-q^3=0,
Q=Aa^2+Bb^2+Cq^2+Daq+Eqt+Tt^2=0
```

in projective three-space. Its genus is four and its canonical bundle is
`O_C(1)`. On `t=1` put

```
J=2Aa^2+Daq-2Bb^2, eta_m=m dq/J.
```

The four holomorphic forms are `eta_1,eta_a,eta_b,eta_q`. Choose the marked
point `P=(a0:0:0:1)`, `a0^2=-T/A`. It is an ordinary point on a generic
coefficient cover. At the actual physical specialization

```
A=B=T=2, C=1/3, D=E=1/2, prime=1009,
```

the determinant of the first four canonical q-jets is `789`, a unit.
Hence the ordinary-point condition is a genuine generic open condition.

## The eight compact representatives

At an ordinary point the first four positive integers are gaps. Thus
`L(4P)` consists of constants and `H0(K+5P)` has dimension eight. A
differential with only a pole at P has zero residue. Therefore the natural
map

```
H0(K+5P) --> H1_dR(C)
```

is injective: an exact such differential would be `df` for `f in L(4P)`.
Both sides have dimension eight, so it is an isomorphism. This includes
all four holomorphic and all four second-kind compact directions.

The projective q-hyperplane section has six distinct points generically:
the four affine points with `q=0,ab=0`, and the two infinity points
`(1:±c0:0:0)`, `c0^2=-A/B`. Its canonical degree is six. Write the
representatives as

```
beta_j = (N_j/q_h^5) times the canonical residue generator,
N_j in H0(O_C(6)).
```

On `t=1` this is exactly `N_j(a,b,q,1)dq/(q^5 J)`. The degree-six
coordinate-ring quotient has dimension 33. Imposing vanishing of the first
five q-jets at the other five hyperplane points gives 25 conditions,
leaving the eight desired forms. All coefficient entries are algebraic in
the universal parameters and in the marked roots. A chosen nonzero
25-by-25 minor gives explicit determinant formulas for their coefficients.

`construct_rr_basis.py` constructs these matrices. At the displayed actual
specialization it checks ideal rank 51 in the 84 degree-six monomials,
quotient dimension 33, jet rank 25, and compact dimension eight. The saved
monomial and pivot data are in `rr-basis-results.json`.

## Complete first-derivative reduction

Let `J_h=2Aa^2+Daq-2Bb^2` be the homogeneous quadratic section. Its
12-point zero divisor is the finite q-ramification divisor, generically
reduced and disjoint from all marked points. Differentiation at fixed
affine q uses

```
a_theta=-a Q_theta/J,
b_theta= b Q_theta/J.
```

It creates only double second-kind poles at this ramification divisor.
Subtracting compact representatives can also leave a pole of order at most
five at P. Every needed exact primitive therefore lies in

```
L(div(J_h)+4P), degree 16, dimension 13.
```

It is constructed as `H6/(J_h q_h^4)` with 20 vanishing q-jet conditions
(four at each other hyperplane point) on the same 33-dimensional degree-six
space. Its derivative space has dimension 12. Thus eight compact columns
plus twelve exact columns give a complete 20-column reduction.

For an affine numerator N and a function numerator H define

```
aqnum=-a Q_q-3q^2 Q_b,
bqnum= b Q_q+3q^2 Q_a,
Jqnum=J J_q+J_a aqnum+J_b bqnum.
```

After clearing the common literal differential denominator `q^5 J^3`, the
compact column is `N J^2` and the exact function column is

```
q J (J H_q+H_a aqnum+H_b bqnum)-q H Jqnum-4H J^2.
```

For the theta derivative of a basis numerator, let `Ndot` denote its
coefficient derivative (the monomial coordinates are fixed). The cleared
target is

```
Ndot J^2+Q_theta(-a N_a+b N_b)J
 -N (partial_theta J)J-N Q_theta(-a J_a+b J_b).
```

The coefficient derivatives are obtained exactly by differentiating the
25 jet equations. If `M B=0`, with the free coordinates of B fixed, then
`M Bdot=-Mdot B`; the same invertible minor solves this derivative.

`compute_gm_at_point.py` constructs all six universal coefficient directions
`A,B,C,D,E,T`. Its 48 identities are checked as polynomial identities modulo
the literal ideal `(Q,ab-q^3)` after clearing the stated denominator. All
48 pass. The complete eight-by-eight matrices and exact primitive columns
are in `gm-at-point-results.json`. The matrix convention is columns:

```
nabla_theta beta_j = sum_i Mtheta[i,j] beta_i+d_q(primitive_j).
```

The generic rational-function construction is the same finite linear
algebra. One may use a fixed homogeneous degree-11 coordinate quotient
instead of a symbolic Groebner calculation: the relevant coefficient and
relation matrices then have entries algebraic in the universal parameters,
and any demonstrated nonzero rank-20 minor supplies adjugate/determinant
formulas. No pole or degree family is searched.

## Actual shear source, including infinity

The source form `q eta_b` has double second-kind poles at the two infinity
points. It is reduced by adding exact primitives in

```
L(4P+P_infty_plus+P_infty_minus), dimension 3.
```

Write these functions as `H5/(q_h^4 t_h)`. The degree-five quotient has
dimension 27. Impose four q-jets at the other three affine q-zero points,
and six at each infinity point (there the denominator has order seven).
The resulting 24 conditions leave three functions including constants.
Together with the eight compact forms, their two nonzero derivative columns
give the complete ten-dimensional source reduction. The pole at infinity
is transported by explicit primitives; it is not discarded.

`reduce_shear_source.py` verifies both `eta_b` and `q eta_b` exactly. At the
displayed specialization, the latter compact vector is

```
[633,15,134,137,0,510,359,0] mod 1009.
```

The exact primitive coefficients and numerator rows are retained in
`shear-source-reduction-results.json`.

## Full ruling-normal-function derivatives

The same construction extends intrinsically to `beta_hat`, retaining its
third-order infinity second-kind pole. Let

```
Rcrit=div(J_h), Rrul=div(b+rho t)=D_plus+D_minus.
```

For first parameter derivatives, all exact primitives lie in

```
L(Rcrit+Rrul+2P_infty_plus+2P_infty_minus+4P),
degree 26, dimension 23.
```

Use `H7/[J_h(b+rho t)q_h^4]`. The degree-seven coordinate quotient has
dimension 39. Impose four q-jets at the other three affine q-zero points
and two at each infinity point: 16 conditions leave 23 functions. Their
22 derivatives plus the eight compact representatives give a complete
30-column reduction of every first derivative of the normalized ruling
form. The finite moving ruling poles and the infinity second-kind terms
are both included.

For second parameter derivatives, the q-ramification pole order becomes
four and the moving ruling pole order becomes three. The exact primitive
space is

```
L(3Rcrit+2Rrul+2P_infty_plus+2P_infty_minus+4P),
degree 56, dimension 53.
```

Use `H12/[J_h^3(b+rho t)^2 q_h^4]`. The degree-twelve quotient has
dimension 69, and the same 16 q-jet conditions leave 53 functions. Its
52 exact columns plus eight compact columns give a complete 60-column
second-derivative reduction. This is a Riemann--Roch pole-divisor bound,
not a bounded nonexistence test.

At the displayed prime, `Cp=200`, `rho^2=521` is a nonsquare, whereas
`lambda^2=898` is a square. Thus beta_hat reduction itself requires the
quadratic field extension `F_1009[rho]/(rho^2-521)`; the compact GM and shear
source computations above already lie in the base prime field. Neither
the normal-function derivatives nor their signed-minor annihilator has yet
been computed in this package.

## The simpler finite-residue chi generator: full physical order-three data

The later generator

```
chi=b dq/(b0 q), b0^2=-T/B
```

has fixed finite residues and no infinity residue, while its fourth-order
infinity second-kind pole is retained. Its first parameter derivatives
have coefficients proportional to `1/J`, so they are regular at the
q-ramification points: `dq/J` is regular there. Consequently its compact
jet reduction has smaller intrinsic pole bounds than beta_hat:

```
order1 primitives: L(3P_inf_plus+3P_inf_minus+4P), degree10/dimension7;
order2 primitives: L(Rcrit+3P_inf_plus+3P_inf_minus+4P), degree22/dimension19;
order3 primitives: L(3Rcrit+3P_inf_plus+3P_inf_minus+4P), degree46/dimension43.
```

They can be constructed with denominators `q_h^4`, `J_h q_h^4`, and
`J_h^3 q_h^4` and numerator degrees 4, 6, and 10 respectively. Impose four
q-jets at the other three affine q-zero points and one at each infinity
point (14 conditions). Thus the complete compact-plus-exact reduction
sizes are 14, 26, and 50 columns. In particular the second-order data saved
here used a complete but unnecessarily enlarged 50-column space; this does
not affect its checked identities. The same space is exactly the intrinsic
third-order one.

The actual physical coefficient map is

```
A=1+R, B=1+S, C=k/3, D=zk/2, E=z/2, T=1+z^6, k^6=RS.
```

All first, second, and third derivatives of this map are included in
`chi_physical_third_jets.py`; no coefficient or root is frozen. At
`R=S=z=k=1` modulo 1009 it verifies all 19 literal cleared identities for

```
R,S,z, RR,RS,Rz,SS,Sz,zz,
RRR,RRS,RRz,RSS,RSz,Rzz,SSS,SSz,Szz,zzz.
```

The first nine columns have rank seven; adding the ten symmetric third
derivatives gives rank eight. The compact pivot derivatives are

```
I=[R,S,z,RR,RS,Rz,SS,RRR].
```

Their exact determinant is `822 mod 1009`, a unit. The complete eight-row
class matrix, eleven kernel rows, and every exact primitive coefficient
are retained in `chi-physical-third-jets-results.json`. All 19 differential
identities were independently checked as cleared polynomial identities
modulo `(Q,ab-q^3)`; this statement concerns the reduction, not independent
validation of the target-jet formula. No pole at infinity is dropped.

### Generic determinant annihilators and scalar current generation

Let `K_j` be the eight compact coordinates obtained by the intrinsic RR
solve for the actual physical jet `partial^alpha_j chi`, and let `p_j` be
its exact fiber primitive. Let M be the eight-by-eight matrix with columns
indexed by I above. On the generic open where its determinant is nonzero,
the following are finite explicit algebraic formulas:

```
lambda_j=M^(-1)K_j=adj(M)K_j/det(M),
L_j=partial^alpha_j-sum_i lambda_ij partial^alpha_i,
L_j chi=d_q[p_j-sum_i lambda_ij p_i].
```

There are eleven free j, indexed by `Sz,zz` and the nine third derivatives
other than `RRR`. These operators retain all eight compact rows. The
specialized nonzero determinant proves that this is a genuine generic
construction; it does not lift any displayed numerical row by itself.
Every RR kernel, exact reduction, and inverse is a fixed finite matrix
over the coefficient-root field, so the formulas are rational determinant
expressions there. Their normalized kernel coefficients are unchanged by
changing the marked-point cover or the common sign of b0, since those
changes are invertible changes of compact basis or common column scaling.

The JSON convention multiplies **every** target jet and primitive by b0.
Thus its M and K_j produce the same lambda_j, but its literal fiber
primitive is `(p_j-sum_i lambda_ij p_i)/b0` when interpreting the stored
primitive coefficients. This common factor does not differentiate along
the curve.

For the physical base volume

```
mu dR dS dz, mu=1/(108 k^5), k^6=RS,
```

the exact scalar source generated by an arbitrary rational multiplier h_j
is the full weighted adjoint

```
L_j^{*,mu}(h_j)
 =(-1)^|alpha_j| mu^(-1) partial^alpha_j(mu h_j)
  -sum_i(-1)^|alpha_i| mu^(-1)
        partial^alpha_i(mu lambda_ij h_j).
```

All derivatives are actual physical derivatives, including those of k,
the RR marked roots, mu, and the determinant coefficients. Green's identity
with the retained fiber primitive gives a literal rational current for
this scalar multiple of chi. Thus eleven arbitrary potentials provide a
complete source-generation interface on this connection chart. Matching
their sum (optionally together with the three toric-box potentials) to the
specific physical forcing remains open. No such match is claimed here.

### Independent literal toric boxes

`verify_toric_chi_boxes.py` passes eight exact groups, including a general
implicit-root third-derivative formula, for the literal boxes

```
(partial_D^2-partial_A partial_C) psi=0,
(partial_E^2-partial_C partial_T) psi=0,
(partial_A partial_B partial_T-partial_C^3) psi=0,
psi=b dq/q=b0 chi.
```

For the last box use
`P=Bb^4+(Cq^2+Eq+T)b^2+Dq^4b+Aq^6`. Its coefficient monomials obey
`P_A P_B P_T=P_C^3=q^6 b^6`. The local-root residue formula

```
partial_i1...partial_in b
 =(-1)^n(n-1)! Res[(P_i1...P_in)/P^n db]
```

therefore proves the equality of the literal derivatives with no boundary
or fiber-exact remainder. Conjugating by b0 gives the normalized cubic box

```
[partial_A(partial_B-1/(2B))(partial_T+1/(2T))-partial_C^3] chi=0.
```

Its passage to coefficient-normalized coordinates carries the explicit
Cartan fiber primitives documented by the parent agent; the literal
universal identity does not authorize discarding those terms.

## Corrected cross-source compact input and its chi operator

The actual cross-source form supplied by the infinity-current calculation is

```
xi=a dq/q, xi2=dq/b,
r=(Cp-E^2/(4T))/(2T), s=D Cp/(2A),
F_b=a/(2q^2)+(D a^2+Ea)/(4Tq),
psi_hat_b=xi2+d_q F_b-r xi+r s q^2dq/J.
```

The last term is mandatory. The raw form `xi2+dF_b-r xi` has a nonzero
infinity residue inherited from xi; it was not reduced as compact. The
corrected form has only infinity poles of order at most five and zero
residues. Its exact primitive space is

```
L(4P+4P_inf_plus+4P_inf_minus), degree12/dimension9.
```

Construct the nine functions as `H4/q_h^4` with four q-jets vanishing at
the other three affine q-zero points. No infinity vanishing condition is
imposed: their four allowed pole orders are explicitly retained. The eight
nonzero exact derivative columns plus the eight compact columns give a
complete 16-column reduction. `reduce_cross_compact_source.py` checks the
literal cleared identity. At the displayed actual specialization its
compact vector is

```
Kpsi=[659,508,683,760,167,390,856,784] mod1009.
```

All eight entries are retained, together with all nine exact-function
coefficients, in `cross-compact-source-reduction-results.json`.

This supplies an actual source-carrying use of the full pivot connection,
beyond homogeneous annihilator generation. Using M from the chi pivot
columns, put

```
c=adj(M)Kpsi/det(M).
```

Then, with the stored b0 convention, the complete source relation is

```
psi_hat_b=sum_i c_i b0 partial^alpha_i chi
          +d_q[p_psi-sum_i c_i p_i].
```

Every exact primitive is retained. At the actual finite-field point the
coefficient vector for `[R,S,z,RR,RS,Rz,SS,RRR]` is

```
[724,723,793,10,976,68,503,597] mod1009.
```

The corresponding determinant construction and convention are saved in
`cross-source-chi-operator-results.json`. These numbers are specialization
data; the generic rational coefficients are the stated determinant
expressions, not constants inferred from the point. For any multiplier h,
Green's identity converts the displayed operator into the scalar forcing

```
sum_i(-1)^|alpha_i| mu^(-1) partial^alpha_i(mu b0 c_i h) * chi,
```

plus an explicit rational current and the retained fiber primitive. The
specific full physical source still has to match the resulting scalar
forcing together with the annihilator-generated sources.

An independent implementation checked the nineteen chi target derivatives
and their compact-plus-exact representatives using multivariate Taylor
Newton solution of the actual quartic at twelve fresh affine curve points.
All 228 literal checks pass, retaining `k^6=RS` and b0 normalization; compact
rank eight and the stated pivots agree. See
`../../audit/ruling/verify_chi_jets_newton.py` and
`../../audit/ruling/chi-jets-newton-results.json`. This is independent
target-jet verification, not a second proof of the global RR theorem.
