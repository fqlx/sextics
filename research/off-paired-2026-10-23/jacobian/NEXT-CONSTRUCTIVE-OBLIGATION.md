# Exact moving-pole current and the remaining constructive obligation

The original certificate is still unsolved. No Lean certificate, protected verification, solve PR or acceptance is asserted.

Use $x=X_1,y=Y_0,z=Y_1$ on $X_0=1$, with

$$
H=1+x^6+y^6+z^6+xyz/2,\quad C=x^3z/2+xy/3,\quad A=y^3,
\quad s=-3z/2,\quad L=H+sC.
$$

On the endpoint family $Z^2=(H+Cp)^2-4p^6$, let

$$
\beta_s=\frac{dp}{(p-s)Z},\qquad \omega_0=dp/Z.
$$

The identity $(\partial_C-s\partial_H)\beta_s=\partial_H\omega_0$ is literal. Define

$$
J=H_xC_y-H_yC_x=L_xC_y-L_yC_x,
\qquad
W=\left(\frac{A L_y}{6J},-\frac{A L_x}{6J},0\right).
$$

Then $W(L)=W(s)=0$, $W(C)=-A/6$, and $W(F_s)=0$ for $F_s=L^2-4s^6$. Consequently the rational moving-pole current has the exact covariant divergence

$$
\sum_i\nabla_i(W_i\beta_s)
=-\frac A6\partial_H\omega_0+\mathcal R\beta_s,
$$

where

$$
\mathcal R=\operatorname{div}W
=\frac{A(L_xJ_y-L_yJ_x)-A_yL_xJ}{6J^2}.
$$

This defect is nonzero: at $x=y=z=1$ it is $-97/1014$. Its finite-pole residue is $\mathcal R/Z_s$, where $Z_s^2=F_s$. Compact current components alone have no finite-pole residue and cannot silently remove this defect. The remaining problem is to construct residue-compatible additional moving-pole currents and compact currents whose total covariant divergence is the physical source. The independent exact checker `moving-pole-current-defect.py` verifies these identities and the general weighted-curl residue identity.

A rational way to impose residue compatibility automatically is

$$
V=\operatorname{curl}P-\frac{\nabla F_s\times P}{2F_s},
\qquad
\operatorname{div}V-\frac{V(F_s)}{2F_s}=0.
$$

This corresponds to the normalized-pole residue two-form $d(\gamma/Z_s)$ and is invariant after multiplying by $\tau_s=Z_s\beta_s$. Searches using polynomial potentials and this identity remain restricted searches; failure does not exclude other currents or certificates.

## Full kernel retained over the source-density quotient

At fixed $L,z$, set $t=x^3$, $u=xy$, $b=3z^2/4$, $B=L-1-z^6$. The complete physical quotient is

$$
u^6=t^2(-t^2+bt+B),\qquad C=tz/2+u/3,
$$

and the exact relative density is

$$
\phi\,dC=-\frac{dt}{18u^2}.
$$

The endpoint kernel on this cover is

$$
\beta_s=\frac{dp}{(p+3z/2)Z},\quad
Z^2=\left[L+(tz/2+u/3)(p+3z/2)\right]^2-4p^6.
$$

The scalar density factors through a genus-two curve and two elliptic curves as recorded in `moving-pole-source-interface.md`, but the kernel retains the sign of $u$. Any elliptic-contraction construction must preserve this full equation or explicitly derive all trace and horizontal corrections. The scalar elliptic differential alone does not supply the required primitive.
