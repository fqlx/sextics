# The actual tangent-hyperplane support has no holomorphic two-form

This is a resolution calculation for one proposed support. It gives no
primitive or certificate for the off-paired target.

Use the exact endpoint split, with `(t,x,y,z)=(X0,X1,Y0,Y1)`:

\[
\begin{aligned}
 H&=t^6+x^6+y^6+z^6+\tfrac12t^3xyz,\\
 C&=x(\tfrac12x^2z+\tfrac13t^2y),\\
 F&=H+X_2^6+Y_2^6+C X_2Y_2.
\end{aligned}
\]

Fix any constant `rho` with `rho^6=-1`. On the hyperplane
`X2=rho*Y2`, the two pure sixth powers cancel exactly. With `b=Y2`,

\[
D_\rho:\quad H+\rho Cb^2=0.
\]

In particular all three original mixed monomials remain: the first is in
`H`, and the other two are in `C`. The target restricts to
`A=t^3y^3`; it has not been replaced by a different density.

## A double-cover model

On `C!=0`, set `w=Cb`. The function field is that of

\[
W:\quad w^2=-\rho^{-1}HC,
\]

a double cover of `P3_(t,x,y,z)` branched over the degree-ten divisor
`B={HC=0}`. Thus any smooth projective resolution of `D_rho` is birational
to a smooth projective resolution of this double-cover model.

The singular quartic `C=0` has a plane component `P:x=0` and a cubic
component

\[
 S:\quad t^2y+\tfrac32x^2z=0.
\]

Its singular line is `L:t=x=0`. The multiplicity of `C` along `L` is
exactly three; `H` does not contain `L`.

## One base blow-up makes the branch simple normal crossing

Let `pi:B0=Bl_L(P3)->P3`, with exceptional divisor `E`, and write `H0`
for the pullback of the hyperplane class. The normalized pullback double
cover has reduced branch

\[
B'=H'+P'+S'+E\ \sim\ 10H_0-2E.
\]

Indeed, the proper transforms of the plane and cubic have classes
`H0-E` and `3H0-2E`, respectively. The odd multiplicity three adds `E`
to the branch. The double-cover line bundle is therefore

\[
\mathcal L=\mathcal O_{B_0}(5H_0-E).
\]

Here the branch is actually simple normal crossing, including at the
special points above `H intersect L`:

* `P'` is smooth. The strict cubic `S'` is its smooth normalization `F1`.
  For example, on the blow-up chart `x=tr`,
  `C=t^3*r*(r^2*z/2+y/3)`, so the branch components are locally
  `t=0`, `r=0`, and `r^2*z/2+y/3=0`.
* `H` is smooth. If all coordinates were nonzero at a critical point,
  putting `M=t^3xyz` in the four multiplied gradient equations would
  give `t^6=-M/4` and `x^6=y^6=z^6=-M/12`. The identity
  `M^6=t^18*x^6*y^6*z^6` would imply
  `M^6=M^6/110592`, a contradiction. A zero coordinate forces all four
  coordinates to vanish. Consequently `H'` is the blow-up of a smooth
  surface at the six transverse points `H intersect L`, and is smooth.
* `H' intersect P'` is the smooth Fermat sextic `t^6+y^6+z^6=0`.
  The curve `H' intersect S'` is also smooth. An explicit normalization is
  `[t:x:y:z]=[r0*k:r1*k:-(3/2)r1^2*l:r0^2*l]`, on which `H` becomes

  \[
  (r_0^6+r_1^6)k^6+
  (r_0^{12}+\tfrac{729}{64}r_1^{12})l^6
  -\tfrac34r_0^5r_1^3k^4l^2.
  \]

  An interior singular point would force a multiple root of
  `p(u)=(64+729u^4)(1+u^2)^2-4u^3`. Its exact gcd with its derivative is
  one. The roots on `k=0` and `l=0` are simple; the two remaining boundary
  fibres have nonzero fibre derivative. This checks the whole surface.
* `E=P1 x P1`. The curve `S' intersect E` maps two to one to `L`, with
  ramification only over `y=0` and `z=0`. The six points of `H intersect L`
  obey `y^6+z^6=0`, and are distinct from these ramification points.
  Thus `H',S',E` meet transversely. Likewise `H',P',E` meet transversely.
* `P',S',E` meet at the single point over `y=0` with exceptional direction
  `x/t=0`; the local equations above have independent gradients there,
  and `H` is nonzero there. Away from `E`, `P' intersect S'` is the line
  `x=y=0`; its six intersections with `H'` have `t*z!=0` and are transverse.
  There is no fourfold branch intersection.

These are exact properties of this `H,C`, rather than generic assumptions
about a quartic branch or a smooth cubic component.

## Cohomology of the normalized cover

The remaining double-cover singularities have local equations
`w^2=u*v` or `w^2=u*v*s`; these are normal toric singularities, hence
rational in characteristic zero. A resolution does not change cohomology
of the structure sheaf. For the finite double cover `q:W0->B0`,

\[
q_*\mathcal O_{W_0}
=\mathcal O_{B_0}\oplus\mathcal O_{B_0}(-5H_0+E).
\]

The blow-up has `pi_*O(E)=O_P3` and no higher direct images. Indeed use
`0 -> O -> O(E) -> O_E(E) -> 0`: the blow-up has no higher structure-sheaf
direct images, and `O_E(E)` restricts to `O_P1(-1)` on the fibres of
`E->L`, so all of its direct images vanish.
Consequently

\[
\begin{aligned}
H^2(W_0,\mathcal O_{W_0})
&=H^2(B_0,\mathcal O_{B_0})
 \oplus H^2(B_0,\mathcal O_{B_0}(-5H_0+E))\\
&=H^2(\mathbb P^3,\mathcal O)
 \oplus H^2(\mathbb P^3,\mathcal O(-5))=0.
\end{aligned}
\]

By rationality of the remaining singularities and Hodge symmetry, every
smooth projective resolution of `D_rho` therefore has `h^{2,0}=0`.
The argument works for all six choices of `rho`.

This closes the proposed tangent-hyperplane support as a source of a
holomorphic two-form whose Gysin image could equal a nonzero `(3,1)`
target. It does not address a support with additional or different
components, and supplies no solution to the original certificate problem.

The companion checker `tangent-hyperplane-support.py` verifies the exact
target split, double-cover substitution, blow-up multiplicity and local
equations, normalized branch restriction, squarefree eliminant, and the
divisor classes used above. The cohomology and rational-singularity steps
are the standard characteristic-zero algebraic-geometric arguments stated
explicitly here, not claims of Lean verification.

Prepared with OpenAI Codex assistance.
