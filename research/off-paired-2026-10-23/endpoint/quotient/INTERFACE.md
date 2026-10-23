# Exact constant-source quotient current

No current or certificate is established. These files retain the actual source after the finite quotient

\[
u=xy,\quad v=y^3,\quad z=Y_1,\quad x=X_1,\ y=Y_0,\ X_0=1.
\]

Since the coordinate Jacobian is `3v`, the physical source satisfies

\[
y^3\,dx\wedge dy\wedge dz=\frac13du\wedge dv\wedge dz.
\]

The coefficient map is retained exactly:

\[
H=1+\frac{u^6}{v^2}+v^2+z^6+\frac{uz}{2},\qquad
C=\frac{u^3z}{2v}+\frac u3.
\]

Thus the endpoint source is

\[
-\frac1{18}\nabla_H\omega_0\,du\wedge dv\wedge dz,
\]

for the previously audited orientation `Z=b^6−a^6`. Homogeneously, multiply the source coefficient by `X0³`, and replace the mixed terms of `H,C` by `X0³uz/2,X0²u/3`.

The weights are `(X0,u,v,z)=(1,2,3,1)`. A current coefficient in coordinate `i` and basis index `j` has weight

\[
w_i-3-2j.
\]

For `D=X0^k v^m`, its numerator has weighted degree `3m+k+w_i−3−2j`. On `X0=1`, weighted monomials below that degree represent the missing powers of `X0`. The remaining sign involution negates `u,v,z,p`; the numerator has parity `m+j+1`. The two finite forms `beta_s` have effective index `j=−1`, and the infinity form `omega2` has index `j=2`.

`constant_density_current.py` keeps the compact four basis forms, the infinity form, and both actual finite poles

\[
s_1=-3X_0z/2,\qquad s_2=-X_0^3v/u^2.
\]

The rational connection includes all derivatives of these poles. Each finite residue equation and the infinity divergence equation is retained. Fixed-denominator tests solve

\[
\sum_i[\partial_iN_i-N_i\partial_i\log D+B_iN_i]
=-\frac{D}{18}M_He_0.
\]

The independent verifier inspected the source, homogeneous weights, parity and all coefficient/pole chain rules and found no discrepancy. The saved finite-field tests are restricted exploratory feedback only.

`constant_density_curl.py` introduces physical discriminant poles through rational vectorpotentials. In quotient coordinates the potential component `A_j` has weight `5−w_j`; its numerator has weighted degree `3m+k+5−w_j` and parity `m+1`. For each actual finite pole, the vector

\[
V=\operatorname{curl}A-\frac{\nabla f(s)\times A}{2f(s)}
\]

satisfies the weighted residue equation identically. The solver includes compact and infinity currents simultaneously. The finite search does not exhaust closed residue forms, arbitrary rational coefficients, or arbitrary serving divisors.

The naive weighted canonical-bundle calculation ignores the `v=0` boundary of the rational coefficient map. No uniruledness or dominant polynomial-curve family is inferred from those weights.

The direct quartic model is

\[
G=v^2F=u^6+v^4+
[1+z^6+a^6+b^6+uz/2+(u/3)ab]v^2
+(u^3zab/2)v.
\]

Its actual density is `v^4 du dv dz da db/(3G²)`. The `E=1` polynomial-primitive check in `direct_quartic_current.py` is already covered by the prior denominator-degree-six exclusion after the exact Piola lift; it produced no hit and is not new progress. The nonnormal `u=v=0` boundary must be retained in geometric arguments about this quartic model.

## Audit of the actual quartic first-current cycle

The Jacobian agent constructed an actual rational first current with
`N(G)=−G/3−v⁴`, `div N=−1/3+h`. The correction is `h/G=h/(v²F)`, so its endpoint Hermite reduction carries the essential prefactor `v⁻²`.

Writing `R=−(H/12+Kbase) MH e0−(C/9+2u/27) MC e0`, where `Kbase=(1+z⁶)/3+7uz/36`, gives the exact identity

\[
\operatorname{div}_\nabla(W\omega_0)=R/v^2-\nabla_H\omega_0,
\qquad W=\left(-\frac{u}{18v^2},-\frac1{3v},0\right).
\]

Indeed `div W=5/(18v²)`, and the Euler relation `e0=−(3H/2)MH e0−C MC e0` verifies both compact coefficients. `first_current_cycle.py` checks five exact rational identities.

Consequently this first-current reduction returns the original source with scalar coefficient **one**. It supplies an integration-by-parts identity, not an invertible scalar cycle or a primitive. Any proposed closure still needs an additional source-carrying current or a separately canceled remainder.

## Compact corrections sharing the physical finite-pole discriminant

`physical_discriminant_correction.py` allows compact and infinity currents `P_i/F_s`, where `F_s=f(s)` for either actual finite pole, simultaneously with the matching residue-closed finite-pole current `V beta_s`. This is broader than polynomial compact currents combined with those potentials.

For compact basis index `j`, the numerator has weighted degree `12+k+w_i−3−2j` and parity `j+1`; the denominator is `X0^k F_s`. The potential component numerator has degree `k+5−w_j` and odd parity. At `X0=1`, the equation after multiplying by `F_s` is

\[
\sum_i[\partial_iP_i-P_i\partial_i\log F_s+B_iP_i]
+F_s\sum_iV_i B_i e_{\beta_s}
=-\frac{F_s}{18}M_He_0.
\]

The finite-pole residue row vanishes identically for the potential current. The infinity residue row remains in the system. Since `B_i[beta_s,beta_s]=−(partial_i F_s)/(2F_s)`, the free numerator derivative is implemented as `partial_i P_i+2B_i[beta_s,beta_s]P_i`.

The small saved tests use pole one with `k=0,1` and pole two with `k=0`. They yield no modular candidate. They do not exhaust rational corrections sharing these poles or any unrestricted certificate space.
