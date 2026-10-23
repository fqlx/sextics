# Moving third-kind pole and the exact physical source

These identities are verified by `moving-pole-and-source-factor.py`. They do not yet give a closed current or a physical certificate.

Let $f(p)=(H+Cp)^2-4p^6$, $Z^2=f(p)$, $Z_s^2=f(s)$, and

$$
\tau_s=\frac{Z_s\,dp}{(p-s)Z},\qquad \omega_j=\frac{p^jdp}{Z}.
$$

Holding $s$ fixed gives the literal identity

$$
(\partial_C-s\partial_H)\tau_s=Z_s\partial_H\omega_0.
$$

The derivative of the moving pole has the exact reduction

$$
\partial_s\tau_s=d_p\left(-\frac{Z}{Z_s(p-s)}\right)
+\frac{8s^4\omega_0+4s^3\omega_1-4s\omega_3-8\omega_4}{Z_s}.
$$

Thus no infinity third-kind basis vector is needed for this particular derivative. For an arbitrary physical derivation $W$,

$$
\nabla_W\tau_s=(W(H)+sW(C))\partial_H\tau_s
 +W(C)Z_s\partial_H\omega_0+W(s)\partial_s\tau_s.
$$

This is an actual source-carrying normal-function identity. It does not remove the residue equation: a current with coefficient field $V$ and normalized residues $\pm1$ needs $\operatorname{div}V=0$. A single pole current with no further compact correction would require

$$
V(s)=0,\quad V(H)+sV(C)=0,\quad Z_sV(C)=A,\quad \operatorname{div}V=0
$$

(up to the common source normalization). These four conditions have not been solved.

For the physical pole $s=-3z/2$, write

$$
L=H+sC=y^6+1+x^6+z^6-3x^3z^2/4.
$$

Modulo $dz$, $d\tau_s=\tau_{s,H}\,dL+Z_s\omega_{0,H}\,dC$. The unique vector satisfying the first three displayed conditions in the $x,y$ plane has a remaining nonzero divergence in general.

## The actual relative density has a bielliptic factor

At fixed $L,z$, put $v=y^2$, $b=3z^2/4$, $B=L-1-z^6$. The curve

$$
v^3=-x^6+bx^3+B
$$

has an order-three quotient preserving $dx/v$:

$$
w=v/x,\quad t=x^3,\quad
R=2t+w^3-b,\quad R^2=(w^3-b)^2+4B,
\qquad \frac{dx}{v}=-\frac{w\,dw}{R}.
$$

After $\kappa^6=b^2+4B$, let $u=w/\kappa$, $V=R/\kappa^3$, $\alpha=-2b/\kappa^3$. Then $V^2=u^6+\alpha u^3+1$ and

$$
X=u+u^{-1},\qquad Y_\pm=V(u\pm1)/u^2,\qquad
Y_\pm^2=(X\pm2)(X^3-3X+\alpha),
$$

$$
\frac{dx}{v}=-\frac1{2\kappa}
\left(\frac{dX}{Y_+}+\frac{dX}{Y_-}\right).
$$

This retains the nontrivial $x$ character missing from the simpler $x^3$ elliptic quotient. However, the full moving-pole kernel depends on $C=x^3z/2+xy/3$. The additional $y\mapsto-y$ quotient used to replace $y$ by $v=y^2$ changes $C$. The full kernel therefore remains on the cover with $u_0=xy$ and $u_0^2=t w$, equivalently

$$
u_0^6=t^2(-t^2+bt+B).
$$

The elliptic decomposition of the scalar density alone is not a primitive for the product with the kernel. Any construction must retain this cover and the resulting horizontal corrections.
