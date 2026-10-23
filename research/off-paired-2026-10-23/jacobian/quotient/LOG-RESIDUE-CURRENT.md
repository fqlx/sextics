# A genuinely nonexact log-residue current with the physical coefficient kernel

This gives an actual rational primitive for an explicit family of rational source coefficients. Matching the immutable source remains open.

Work on the physical base $(x,y,z)$, with

$$
H=1+x^6+y^6+z^6+xyz/2,\quad C=x^3z/2+xy/3,\quad
s=-3z/2,\quad L=H+sC,\quad T^2=L^2-4s^6.
$$

On the endpoint curve put $Z^2=(H+Cp)^2-4p^6$, $\omega_0=dp/Z$, and $\beta_s=dp/((p-s)Z)$. Define

$$
r=\frac{L+T}{2s^3},\qquad
\theta=d\log r=\frac{dL-3L\,dz/z}{T}.
$$

For any nonzero rational base function $g$, the two-form $\theta\wedge d\log g$ is closed. Its associated rational beta-current vector is

$$
V=\left(\nabla L-\frac{3L}{z}\nabla z\right)\times\frac{\nabla g}{g}.
$$

It satisfies the exact identities

$$
\operatorname{div}V=3V_z/z,\qquad V(L)=3L V_z/z,\qquad V(s)=s V_z/z,
$$

$$
\operatorname{div}V-\frac{V(T^2)}{2T^2}=0.
$$

Set

$$
d_g=V(C)-2C V_z/z,\qquad k=V_z/z.
$$

The full, unreduced endpoint identity is

$$
\sum_i\nabla_i(V_i\beta_s)
=d_g\nabla_H\omega_0
-k\,d_p\left(\frac{p}{(p-s)Z}\right).
$$

This includes the endpoint-exact term. With $\Omega=dx\wedge dy\wedge dz$, the rational three-form

$$
\nu_g=\beta_s\wedge\iota_V\Omega
-k\frac{p}{(p-s)Z}\,\Omega
$$

therefore satisfies

$$
d\nu_g=\Omega\wedge d_g\nabla_H\omega_0.
$$

The checker `log-residue-source.py` verifies the cleared endpoint identity and the physical vector identities. No replacement of the physical $H,C$ or their derivatives occurs.

## Why this is more than a curl potential

For $g=J=H_xC_y-H_yC_x$, the log-residue class is genuinely nonexact as a rational two-form. At $x=y=z=1$,

$$
\det\frac{\partial(L,J)}{\partial(x,y)}=-657/4\ne0.
$$

Thus the residue-cover function field is finite over the rational field $\mathbb C(r,J,z)$: $L=s^3(r+r^{-1})$, $T=s^3(r-r^{-1})$, and the nonzero Jacobian establishes dominance. In that rational field, $d\log r\wedge d\log J$ has iterated residue one at $r=J=0$, hence is not exact. A rational primitive upstairs would descend by normalized trace, contradicting this residue. Consequently this class is not of the previously searched form $d(\gamma/T)$.

## Remaining source equation

The immutable physical source requires the coefficient $-y^3/6$ multiplying $\nabla_H\omega_0$ (with base volume written first). A linear combination of the constructed $d_g$ sources and additional compact currents must equal this exact coefficient. No such combination has yet been verified. For $g=J$, the current has the actual $J$ and $z$ poles; a correction ansatz must retain them.
