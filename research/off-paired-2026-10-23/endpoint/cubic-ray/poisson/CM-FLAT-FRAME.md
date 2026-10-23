# Actual flat CM frame and the paired-translation gap

The source is still `R dx da du dv`, with `R=Bp/g^3`, `g=B+3Cp^2`, and
the exact original cubic-ray coefficients. No source current is asserted.

Adjoin `r,s` with

```
r^3=x^6+a^6=H-1, s^3=u^6+v^6=C-1.
```

The following four fields commute and preserve the actual physical volume:

```
RX=(x*d_x+a*d_a)/r,
TX=(a^5*d_x-x^5*d_a)/r^2,
RY=(u*d_u+v*d_v)/s,
TY=(v^5*d_u-u^5*d_v)/s^2.
```

Their duals are the four closed rational one-forms

```
dr/2, etaX=(a dx-x da)/r,
ds/2, etaY=(v du-u dv)/s.
```

The normalizations are essential: `RX(r)=2`, `TX(r)=0`, `etaX(TX)=1`, and
`etaX(RX)=0`. Each radial divergence is `2/r-2(H-1)/r^4=0`, and each
angular coefficient is constant along its own Hamiltonian field. The
commutator identity `[E_X,X_H]=4X_H` cancels the derivative of `r^-2`.

The exact volume and source in this frame are

```
Omega=dx da du dv=-dr ds etaX etaY/4,
R Omega=-W/[4(1+r^3)(1+s^3)] dr ds etaX etaY,
W=CH R.
```

This is a genuine commuting, volume-preserving frame. A variable
coefficient times one of its fields acquires the derivative of that
coefficient in its divergence; the frame does not integrate the source
automatically.

## A fixed elliptic quotient with the correct differential

The X-angle differential has an explicit fixed elliptic quotient:

```
e=r^2/(x^2*a^2), w=(x^6-a^6)/(x^3*a^3),
E_CM: w^2=e^3-4,
etaX=de/(2w),
TX(e)=2w, TX(w)=3e^2, RX(e)=RX(w)=0.
```

The Y-angle factor has the identical construction. On `E_CM`, the point
`P=(0,2i)` has order three. Its translation preserves `etaX` and fixes the
external radial coordinate. Over constants, `X=2^(2/3)e,Y=2w` identifies
this elliptic curve with the S3 Galois elliptic curve `Y^2=X^3-16`, carrying
P to `(0,4i)`.

This is an isomorphism of the fixed elliptic curves, not an identification
of their physical coefficient maps. The S3 translation fixes
`b=B/(H^(2/3)C^(1/3))`; translating the physical CM angle generally changes
the full rank-three B. Their incidence must still be constructed explicitly.

Translation on the elliptic quotient is a finite correspondence on the
original Fermat cover, not a global automorphism of that cover. Its branch
set maps to `{P,-P}`, which is not stable under translation by P. The
finite pullback correspondence preserves the pulled-back angle
differential and hence the physical volume when the radial coordinates
and other angle are fixed. An order-three action can be formed on a
suitable join of its three translates, but no current for the required
physical source pair has been obtained here. Density invariance alone
does not justify applying a group-ring inverse.

## Root characters and trace

Under `r -> zeta*r`, the characters of `dr,etaX` are `+1,-1` modulo
three. The elliptic coordinates have characters `e:+2,w:0`. In
particular `etaX` by itself has zero root trace; its product with `dr`
is invariant and carries the actual physical area. The CM automorphism
`(e,w)->(zeta^2 e,w)` fixes P and commutes with its translation. These
facts keep the finite-correspondence construction compatible with the
root trace but do not supply an invariant source primitive.

The three coupling weights remain visible after adjoining sixth roots
`alpha^2=r,beta^2=s` and normalizing the Fermat angles:

```
B=alpha*beta*xi*nu/2
 +alpha^4*beta^2*xi^3*etacurve*nu*varpi/2
 +alpha^2*beta*xi*etacurve*varpi/3.
```

Neither physical angle translation nor a radial translation leaves this
whole expression unchanged. All its derivatives must remain in a paired
current calculation.

`cm_flat_frame.py` passed 19 exact identities for the frame, closed duals,
volume, elliptic quotient and differential, and root-character checks.
The unresolved constructive obligation is an actual current for a physical
paired source or a solution of the complete coupled rank-two current.
The former pure-vector target `div(A)=0`,
`A(log(kappa))=-1/(2HC)` is now excluded by the separate proper Fermat
moment in `PURE-COMPONENT-SCOPE.md`; allowing all coefficient directions
to vary does not evade that restricted obstruction.
