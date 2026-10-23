# Actual first quartic current and its coefficient-one cycle

The exact checker `lifted-quartic-current.py` constructs a rational current with the right source plus a nonzero correction. It is not a certificate.

Let $r=ab$, $s_0=a^6+b^6$, $\Delta=a^6-b^6$, and

$$
K_0=S/3+uz/36-ur/27.
$$

In coordinate order $(u,v,z,a,b)$, put

$$
N_u=-u/18,\quad N_v=-v/3,\quad N_z=0,\quad
N_a=\frac{a(K_0-b^6)}{6\Delta},\quad
N_b=\frac{b(a^6-K_0)}{6\Delta}.
$$

Direct rational identities give

$$
N(G)=-G/3-v^4,\qquad\operatorname{div}N=-1/3+h,
$$

$$
h=4/9-\frac{s_0K_0-2r^6}{\Delta^2},\qquad
G\operatorname{div}N-N(G)=v^4+Gh.
$$

Thus this is an actual first current for the actual source $v^4/(3G^2)$, leaving the correction $h/(3G)$. It is nonzero, for example $h=45151/428652$ at $u=v=z=a=1,b=2$.

## The physical factor cannot be dropped

Since $G=v^2F$, the remaining correction is

$$
\frac{h}{3G}=\frac{h}{3v^2F}.
$$

Its endpoint residue carries an essential factor $v^{-2}$. With $Z^2=(H+Cp)^2-4p^6$, exact endpoint Hermite reduction gives

$$
h\frac{dp}{Z}\equiv\mathcal R,
\qquad
\mathcal R=-(H/12+K_{\rm base})\nabla_H\omega_0
 -(C/9+2u/27)\nabla_C\omega_0,
$$

$$
K_{\rm base}=(1+z^6)/3+7uz/36.
$$

The physical residual is proportional to $v^{-2}\mathcal R$, not $\mathcal R$ alone.

The endpoint agent identified, and `check-first-current-cycle.py` independently verifies, the rational base current

$$
W=\left(-\frac{u}{18v^2},-\frac1{3v},0\right),
\qquad
\operatorname{div}W=\frac5{18v^2},
$$

for which the compact Euler identity yields

$$
\operatorname{div}(W\omega_0)=\frac{\mathcal R}{v^2}-\nabla_H\omega_0.
$$

The cycle coefficient is exactly one. This current returns the original cohomology class; it supplies no invertible finite operator closure and no solution. An additional source-carrying current or geometric construction is still required.
