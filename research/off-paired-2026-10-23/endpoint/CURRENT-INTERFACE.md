# Exact endpoint current interface

No certificate is established. The original unpublished draft was unavailable in this cloud workspace; these files independently reconstruct its rank-four connection and add an infinity third-kind component.

Use `x=X1,y=Y0,z=Y1,a=X2,b=Y2` on `X0=1`,

\[
H=1+x^6+y^6+z^6+xyz/2,\quad C=x^3z/2+xy/3,\quad p=ab,
\quad Z=b^6-a^6.
\]

Then `Z²=(H+Cp)²−4p⁶`. The square-root orientation matters: the displayed orientation and the residue convention `dF/F` first give the source

\[
-\frac{y^3}{6}\nabla_H\omega_0\,dx\wedge dy\wedge dz,
\qquad \omega_j=p^jdp/Z.
\]

`reconstructed-connection.json` stores columns, so
`∇v omega_j=sum_k Mv[k,j] omega_k`, not the transpose. It also stores rational polynomials `R_vj(p)` such that the exact Dwork identity is

\[
-p^j f_v/2=f\sum_k M_v[k,j]p^k+fR'_{vj}-f'R_{vj}/2,
\qquad f=(H+Cp)^2-4p^6.
\]

The common denominator is `L=4H(4C⁶−729H⁴)`.
The compact basis is `j=0,1,3,4`. The independently added `j=2` form has constant nonzero opposite residues at the two infinities, so its parameter derivatives reduce to the compact basis. `third-kind-connection.json` gives those two compact columns and exact Dwork primitives. The fifth row of the extended connection is zero; cancellation of the current's infinity residues therefore imposes `div(a_2)=0`.

A source-carrying current is a tuple of coefficient columns `a_x,a_y,a_z` satisfying

\[
\sum_{i=x,y,z}\left(\partial_i a_i+
(M_H H_i+M_C C_i)a_i\right)
=-\frac{A}{6}M_He_0,
\quad A=X_0^3Y_0^3.
\]

Here `X0` is held constant by every derivative. This is an exact cohomological current equation; an actual solution must still be transported with its Dwork exact corrections to the original finite certificate, with legal denominator and the prescribed homogeneous degrees. These files do not make that final transport automatically.

For a fixed homogeneous denominator `D` of degree `d`, put `a_i,j=N_i,j/D` with `deg(N_i,j)=d+1−2j`. Clearing the equation gives the polynomial vector identity

\[
\sum_i\big[L(D\partial_iN_i-N_i\partial_iD)
+D((LM_H)H_i+(LM_C)C_i)N_i\big]
=-AD^2(LM_H)e_0/6.
\]

The degree follows from `wt(omega_j)=2j−4`; for `j=2` the numerator degree is `d−3`. The cyclic order-six symmetry has affine weights `(x,y,z)=(2,1,3)`. For an eigencharacter-`delta` denominator, a numerator in output basis `j` and coordinate `i` has character `3+delta+w_i−3j` modulo six. For `2C³±27H²`, retain both character cosets (equivalently average only under the order-three subgroup).

`current_search.py` and `third_kind_current_search.py` implement fixed-denominator modular evaluation screens. They use at least one generic point per unknown, not merely one point per four or five output components: those components can impose dependent sampled conditions. Early undersampled apparent hits were rejected at 400 fresh points and are not retained as candidates. Every retained hit would require fresh-point checks, exact rational reconstruction, full polynomial verification, and original-target transport. Inconsistent modular evaluation systems are restricted search feedback only; they do not establish unrestricted nonexistence or even a characteristic-zero rank certificate by themselves.

## Finite moving pole, beyond the compact and infinity systems

Let
\[
\beta_r=\frac{dp}{(p-r)Z},\quad f_r=f(r)=(H+Cr)^2-4r^6.
\]

This is rational before adjoining a square root. Its residues are `±1/sqrt(f_r)`. `moving-pole-connection.json` stores three five-entry columns for derivatives in `H,C,r`, in basis `(omega0,omega1,omega3,omega4,beta_r)`, plus rational `R_v(p)` for the exact correction `d_p(R_v/Z)`. The coefficient in the beta row is `−(∂v f_r)/(2f_r)`. For `v=r`, this means the derivative of the evaluation, `f'(r)`, and the exact correction includes `−1/((p−r)Z)`.

The compact column can be computed by the ordinary degree-five Dwork reduction of
\[
Q_v(p)=\frac{f_v(r)f(p)-f(r)f_v(p)}{2f(r)(p-r)},
\]
where for `v=r` take `f_v(p)=f'(p)`. The numerator is divisible by `p−r`.

Crucially, directly on rational differentials, with `r` held fixed,
\[
(\partial_C-r\partial_H)\beta_r=\partial_H\omega_0.
\]
Thus this extension has a literal source-carrying normal variation. It does not itself solve the coefficient-divergence equation.

The physical choice `r=−3X0 Y1/2` has weight two and cancels the physical `Y0`-linear term. On `X0=1`,
\[
L=H+rC=y^6+K(x,z),\quad K=1+x^6+z^6-3x^3z^2/4,
\quad f(r)=L^2-4r^6.
\]

For the current search, the beta form has weight `−6`, so its coefficient numerator has degree `d+3` (the code tags it by effective index `j=−1`). Its diagonal connection is retained; the beta equation is the weighted-residue condition `div(b)−b(log(f(r)))/2=0`, not ordinary divergence zero. `moving_pole_current_search.py` uses the full physical derivative including `r_z=−3X0/2`; it clears with `L_old*f(r)`. Its fixed-denominator modular screens are exploratory only.

The actual source density transports as follows. Write
\[
J=H_xC_y-H_yC_x,\quad\phi=y^3/J.
\]
At fixed `L,z`,
\[
\phi\,dC=-\frac{dx}{6y^2}.
\]
Setting `v=y²` gives the physical base curve
\[
v^3=-x^6+\frac{3z^2}{4}x^3+(L-1-z^6),
\]
so this differential really descends to that curve. This is the source-carrying curve used in the separate bielliptic investigation, not an arbitrary polynomial density.

The tempting primitive `(+phi/6) dL∧dz∧beta_r` differentiates to the desired compact source **and** the nonzero beta correction
\[
-\frac{\partial_C\phi|_{L,z}}6\,dL\wedge dC\wedge dz\wedge\beta_r.
\]
That correction remains an explicit obligation. No cancellation, finite-certificate transport, or Lean proof is claimed here.

## Two elliptic quotient densities

The source curve above has `b=3z²/4`, `B=L−1−z⁶` and equation `v³=−x⁶+b x³+B`. Put
\[
w=v/x,\quad T=x^3,\quad R=2T+w^3-b.
\]
Then
\[
R^2=(w^3-b)^2+4B,\qquad dx/v=-w\,dw/R.
\]
Let `c=b²+4B`, and take the finite generic extension `h²=c`, `a³=h`. Setting `w=a u`, `R=h V` gives
\[
V^2=u^6-2(b/h)u^3+1.
\]
The two elliptic quotients are
\[
\xi=u+u^{-1},\quad \eta_\pm=V(u\pm1)/u^2,\qquad
\eta_\pm^2=(\xi\pm2)(\xi^3-3\xi-2b/h).
\]
Their differentials retain the actual density:
\[
\phi\,dC=-\frac{dx}{6v}
=\frac{a^2}{12h}
\left(\frac{d\xi}{\eta_+}+\frac{d\xi}{\eta_-}\right).
\]
`bielliptic_density.py` checks eight exact identities, including the curve equations and the density. This is source transport only. It supplies neither an elliptic scalar primitive nor cancellation of the beta correction described above.

## Two finite poles and automatic residue currents

`two_pole_current_search.py` adds the second physical pole
\[
s_2=-X_0^3Y_0/X_1^2,
\]
which cancels the `Y1`-linear term of `H+C s2`. It keeps each pole's separate weighted residue equation. `two_pole_infinity_current_search.py` also retains the infinity form `omega2`.

A further constructive ansatz builds the physical discriminant poles into the current. For a rational vectorpotential `A` and `F_s=f(s)`, set
\[
V=\operatorname{curl}A-\frac{\nabla F_s\times A}{2F_s}.
\]
Then `div V−V(F_s)/(2F_s)=0` identically. This is the rational form of `sqrt(F_s) curl(A/sqrt(F_s))`; the square root is absent from the resulting coefficients. `weighted_curl_current_search.py` searches these currents for both finite physical poles, simultaneously with compact and infinity currents. Its vectorpotentials have weight four and coefficients represented by affine polynomials up to degree `k+4`, corresponding to powers of `X0` in their denominator. Exact potentials are a sufficient subspace; closed residue forms with logarithmic periods are not exhausted by this ansatz. A failed finite search does not close the route.
