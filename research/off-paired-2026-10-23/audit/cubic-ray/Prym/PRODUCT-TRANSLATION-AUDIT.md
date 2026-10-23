# Independent Prym product translation and source audit

All proposed relative translation identities are correct, with the stated
differential conventions. The independent standard-library Fraction verifier
`verify_product_translations_fraction.py` passes 35 exact groups. It uses no
primary generator or SymPy verifier. Results are in
`product-translations-fraction-results.json`.

This is an audit of an actual source interface and its explicit partial
current. It is not a closed source-carrying primitive or a certificate.

## Full product, area and translations

Put `u=q_plus`, `v=q_minus`, `K=1+z^6-H` and

    s^2=2u^3-zu/2-K,
    d^2=-2v^3-zv/2-K,
    eta_plus=du/s, eta_minus=dv/d,
    area=eta_plus wedge eta_minus.

H,z are parameters for the following relative assertions. The vector fields

    Dplus=s partial_u+(3u^2-z/4)partial_s,
    Dminus=d partial_v+(-3v^2-z/4)partial_d

preserve their actual curve equations. Their cross derivatives commute, and
both are dual to the corresponding displayed elliptic one-form. Thus

    W=Dplus+Dminus,
    Wprime=Dplus-Dminus,
    i_W area=eta_minus-eta_plus,
    i_Wprime area=eta_minus+eta_plus.

Both have zero relative area divergence, and both preserve the two relative
elliptic differentials. Consequently the two flux forms are also invariant
under either relative translation. This is not an absolute assertion in H,z.

For `delta=u-v` and `Cext=(u+v)/6+z(s+d)/4`, the complete product formulas are

    W(delta)=s-d,
    Wprime(delta)=s+d,
    W(Cext)=(s+d)/6+(3z/4)(u^2-v^2)-z^2/8,
    Wprime(Cext)=(s-d)/6+(3z/4)(u^2+v^2).

The off-diagonal correction terms are essential.

## Diagonal and immutable-source normalization

Only now restrict to `u=v=q`, and put

    a=(s+d)/2=x^3, b0=(s-d)/2=q^3/a=y^3.

Both physical identities are checked against the original endpoint H,C
functions. In particular `P_a|H,C=a J`, where
`J=H_x C_y-H_y C_x`. The full normal velocities and endpoint derivatives are

    W(delta)=2y^3, Wprime(delta)=2x^3,
    W(Cext)=a/3-z^2/8,
    Wprime(Cext)=y^3/3+(3z/2)q^2.

Using `P_a|q=2asd` and `dC=P_a|H,C dq/(3P_a|q)`, the flux normalizations are
exactly

    diag(i_W area)=12*(y^3/J)dC=12 phi dC,
    diag(i_Wprime area)=12*(x^3/J)dC.

Thus the companion source is the physical X1-cube density, not X2. The
endpoint source `-phi nabla_H(omega0)/6` correspondingly has the base flux
factor `-1/72` times `diag(i_W area)` when the endpoint fiber-first and
base `(H,C,z)` ordering are kept. Using `dq/(2s)` in place of the stated
`dq/s` would require changing all translation and normalization factors.

## Differentiation cannot be restricted prematurely

The ideal of the diagonal is not preserved by W or Wprime. Their generic
normal velocities are nonzero, so neither defines a derivation of the
diagonal function field by simple restriction.

Exact full second derivatives are

    W^2 Cext=Wprime^2 Cext
      =(u^2-v^2)/2-z/12+(3z/2)(us-vd),
    W^2 delta=Wprime^2 delta=3(u^2+v^2),
    W Wprime delta=3(u^2-v^2)-z/2.

In particular

    diag(W^2 Cext)=-z/12+3zq*y^3.

If the first derivative is replaced by its diagonal expression
`a/3-z^2/8` before applying W, its obvious ambient extension gives only
`-z/12`. The lost `3zq*y^3` term is generically nonzero and is checked
exactly. Iterated derivatives must remain on the product until all
differentiations are completed.

Since Cext is a sum of a function on each factor, all higher iterates have
the valid separated recurrence

    W^n Cext=Dplus^n(u/6+zs/4)+Dminus^n(v/6+zd/4),
    Wprime^n Cext=Dplus^n(u/6+zs/4)+(-1)^n Dminus^n(v/6+zd/4).

This is a useful construction rule, without a claim that the endpoint
current closes after finitely many of these scalar derivatives.

## Exact elliptic terms and the first actual current

The q-square terms have literal exact reductions on each elliptic factor:

    q_plus^2 eta_plus=ds/3+z eta_plus/12,
    q_minus^2 eta_minus=-dd/3-z eta_minus/12.

These identities do not permit discarding their exact terms after multiplying
by the endpoint kernel. Integration by parts creates physical C derivatives.
The independent generic cubic polynomial check also verifies the first
elliptic Gauss-Manin column used by
`endpoint/cubic-ray/background-elliptic/first_prym_current.py`, including its
q-times-elliptic-differential second-kind component and exact primitive.

In that first-current construction let

    theta=(1/d-1/s)/12,
    theta_H=(1/s^3-1/d^3)/24,
    C_H=z(1/s+1/d)/8.

Then `C_H theta=zq^3/(24s^2 d^2)`, including the exact factor. With fiber-first
orientation `J0=omega0 wedge theta dq wedge dz/6`, exterior differentiation
gives

    source-dJ0=(C_H theta omega_C+theta_H omega0)/6.

The primary J0 sign is therefore correct. Reducing theta_H by its exact
elliptic primitive tau and adding
`Jtau=tau omega0 wedge dH wedge dz/6` gives

    source-d(J0+Jtau)
      =[(C_H theta-tau C_q)omega_C+theta_H_cohom omega0]/6.

The complete `C_q` term is necessary. Its mixed `1/(s*d)` numerator is
nonzero already at the actual parameter specialization `q=z=1,H=3`:
it is `-646/11663`. Hence the third genus-two-quotient term is present,
consistent with the primary implementation; it cannot be removed by treating
the two elliptic densities independently.

## Absolute scope

For example at fixed u,v, the parameter derivatives are

    s_H=1/(2s), d_H=1/(2d),
    s_z=-(6z^5+u/2)/(2s),
    d_z=-(6z^5+v/2)/(2d).

Thus `partial_H(area)=-(1/(2s^2)+1/(2d^2))*area` is generally nonzero.
The relative divergence-free statement does not make area an absolutely
closed form on the total family. Full H,z variations, the endpoint parameter
Cext, exact elliptic and endpoint fiber corrections, and the complete source
equation all remain. The companion flux and second-kind data provide valid
constructive components, not a certificate by themselves.

No certificate has been found.
