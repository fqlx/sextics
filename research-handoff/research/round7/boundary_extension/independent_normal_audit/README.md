# Independent audit of the boundary normal charts

The old five numerical pairings are **not** necessary extension conditions.
Their dual test sections have poles at the 24 roots of `P`; the proposed
six-dimensional kernel must not be used as a Hodge-theoretic restriction.

Write `J=1+q^6`, `P=11664 J^4-q^6`, and let `G` be the degree-24 conductor
polynomial from `j0_boundary.json`. The intrinsic twist coordinate in this
note is `U`, with `U^2=s/v`. On the boundary

`U^6 = constant * P G^2/J^12`.

The normalized boundary has genus 103. At each of the 24 simple `P` roots
there is one point of ramification index 6; at each of the 24 simple `G`
roots there are two points of ramification index 3. The other places do
not ramify. Thus `2g-2=-12+24*5+48*2=204`.

The actual local calculation at a `P` root is the decisive correction.
Let `hP=+2` or `-2`, and `tP=-qP^4/(72 J(qP))`. Substitute

```
q=qP+U^6 Q,
h=hP+U^6 H,
t=tP+U^4 T,
v=U^10 n.
```

The three equations, divided respectively by `U^24,U^16,U^6`, have limiting
equations

```
16 H^3 (Sq Q-54 J^2 H)+24 J hP H^2 n+3 tP n^2 = 0,
(24 J hP H^2+6 tP n) T-8 ell n = 0,
Cq Q+Ch H+4 ell = 0.
```

Here `Sq` is the q derivative of `q^3-54 hP J^2`, and `Cq,Ch` are derivatives
of `tP^3+a0*tP+b0` holding `tP` fixed. At `n=0`, the boundary has nonzero
`H0`. The implicit Jacobian is a unit. This can also be seen without
expanding its constants: the first and third equations have independent
`(Q,H)` derivatives because the boundary function `U^6(q)` has a simple
zero at `qP`; the second has nonzero T derivative. Consequently this
strict transform is a smooth surface with coordinates `(U,n)` and
**the normal derivative of v has order 10**.

The exact all-root QQ verification is in
`/workspace/research/round7/moving_j0_audit/P_normalization_chart.py` and
its JSON output. I independently derived the limiting equations and
the implicit-function argument above before comparing that packet.

The old dual sections reconstructed from the trace formula are

`psi_j = ell*q^(j+3)*J^2/G * U dq tensor partial_v`, `0<=j<=4`.

At a P point, `ord(U dq)=6`; all the other displayed factors are units.
As `partial_v=U^-10 partial_n` along the curve, `psi_j` has order `-4`.
They therefore cannot be paired as global sections of `K_C tensor N`.

At G points, a separate initially concerning issue is harmless. After
eliminating h and t, use `alpha=U^2`. The scalar equation has a simple
double G zero at alpha=0. Its critical-value coefficients of alpha and
alpha^2 vanish identically; the latter is the exact identity
`4AC-B^2=0` modulo G. Parametric Morse lemma gives
`unit*(q-Q(alpha,v))^2+alpha^3*T(alpha,v)=0`, with T a unit. With alpha=U^2,
normalization consists of two smooth `(U,v)` sheets. Thus normal v order
is zero at G points. This was independently checked by off_paired in
`../conductor_normalization.py` and by cycle_geometry's exact packet.

The q=0, q=infinity and J=0 charts are independently computed in
`../other_normal_charts.py`: normal orders are 3,3,0 respectively. These
give a model with a regular conormal section represented by v whose
zero divisor has degree at least

`24*10 + 6*3 + 6*3 = 276`.

Hence on this model `deg(K_C tensor N)<=204-276<0`: the dual first-order
extension space is zero. This does not construct a global holomorphic
one-form, establish the Albanese of the entire surface, or solve the
original certificate problem. It does invalidate the five proposed
first-order tests on this model. A different compactification would
need its own complete chart calculation before yielding new tests.
