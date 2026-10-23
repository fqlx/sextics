# Explicit nonexact conic-residue currents

No primitive for the fixed physical source is established. This note retains the actual source and distinguishes conic logarithmic residue classes from rational-exact curl potentials.

Use the constant-density quotient coefficient map from `INTERFACE.md`, and put

\[
s=-3z/2,\quad L=H+sC,\quad F_s=L^2-4s^6,\quad T^2=F_s,
\quad r=\frac{L+T}{2s^3},\quad\beta_s=\frac{dp}{(p-s)Z}.
\]

The identity

\[
T\,d\log r=dL-3L\,ds/s=dL-3L\,dz/z
\]

includes the derivative of the conic scaling parameter. Omitting that term gives an incorrect closed-residue assertion away from wedging with `dz`.

For any rational function `g` (or algebraic function with rational `dlog g`), set

\[
\lambda=\nabla L-3L\nabla s/s,\quad
V=\lambda\times\nabla\log g.
\]

Then `i_V(du∧dv∧dz)=T dlog r∧dlog g`, so the normalized finite-pole residue form is closed. The coefficients of `V` are rational; no logarithm enters the candidate primitive. The exact identities are

\[
V(L)=3L V(s)/s,\qquad
\operatorname{div}V=3V(s)/s=V(F_s)/(2F_s).
\]

Using the **raw** endpoint differentials, including the vertical correction, gives

\[
\sum_i\nabla_i(V_i\beta_s)
=d_g\nabla_H\omega_0
-\frac{V(s)}s\,d_p\left(\frac{p}{(p-s)Z}\right),
\qquad d_g=V(C)-2C V(s)/s.
\]

The displayed vertical exact form can be restored explicitly. Thus these are actual source-carrying currents for the scalar source `d_g`, not merely a hypothetical residue-space enlargement.

For `g=x`, use `dlog x=du/u−dv/(3v)`. Direct simplification gives

\[
V_z=-2v/u,\quad V(C)=\frac{L_z-3L/z}{9v}-u^2,
\]

and hence

\[
d_x=u^2+\frac{z^5}{3v}
-\frac{1+u^6/v^2}{3vz}+\frac vz+\frac{u^3z}{12v^2}.
\]

The logarithmic current is rational after taking the product of the two anti-invariant factors under `T↦−T`. The same construction for `g=y,z` uses `dlog y=dv/(3v)` and `dlog z=dz/z`. Their explicit coefficients are in `log-residue-identities-results.json`.

For the simpler form `dlog r∧dz`, the vector is `V0=∇L×∇z`; it satisfies `V0(s)=V0(L)=div V0=0`, and literally carries source

\[
V_0(C)\nabla_H\omega_0,
\quad V_0(C)=\frac{2v}3-\frac{2u^6}{3v^3}
+3u^2z+\frac{u^3z^2}{4v^2}.
\]

Multiplication by any rational function of `L,z` preserves its closed residue form. However `V0(C)` varies on the fixed-`L,z` curve (`V0(V0(C))=−97/16` at `u=v=z=1`), so choosing a coefficient rational only in `L,z` cannot turn this bare current into the required constant source. This does not exclude compact corrections or other residue forms. The actual source symmetry also requires the appropriate odd coefficient in `z` for this `dz` version; the `dlog g` versions already have the target parity.

## What the conic relation classifies

Locally away from `z=0`, write `s=s0 z`, `ell=L/z³`, `tau=T/z³`. Then

\[
\tau^2=\ell^2-4s_0^6,\quad
\ell=s_0^3(r+r^{-1}),\quad
\tau=s_0^3(r-r^{-1}),\quad d\ell/\tau=dr/r.
\]

Consequently a rational one-form in this conic variable is, modulo rational exact forms, determined by its finitely many residues on the rational `r`-line. The anti-invariant sector has opposite residues at reciprocal points. Its basic class without additional finite poles is `dlog r`; a reciprocal pair `rho,rho^-1` supplies the class `dlog[(r−rho)/(r−rho^-1)]`. Fixed points `r=±1` have zero residues in the anti-invariant sector. Polynomial coefficients in `ell` introduce no new finite residue classes; rational coefficients can introduce additional explicit pole classes.

Wedging these relative conic forms with `dz` gives closed two-forms for arbitrary coefficient functions of `L,z`. This classifies the conic pullback sector modulo relative exactness. It is **not** a classification of all rational closed two-forms on the full physical three-coordinate cover. The additional `dlog r∧dlog g` families above are retained separately.

`log_residue_identities.py` passes 15 exact identities, including the raw source-plus-vertical-exact formula. `log_residue_correction.py` appends the three genuine classes `g=x,y,z` to the previously tested same-`F_s` compact and exact-curl correction spaces at the same two small degree settings. No modular candidate emerged. No degree or unrestricted nonexistence statement follows.
