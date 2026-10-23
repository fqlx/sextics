# Source-first Prym current and the retained mixed correction

This is a literal current for the immutable source, with an explicit
nonzero remainder. It is not a primitive or a certificate. Work over a fixed
characteristic-zero field k; k=C gives the full certificate contract.

Use the background source interface in
`../../../coupled-fresh/infinity-horizontal/BACKGROUND-ELLIPTIC-SOURCE.md`.
In coordinates H,q,z the background functions are

    K0=1+z^6-H,
    s^2=2q^3-zq/2-K0, d^2=-2q^3-zq/2-K0,
    C=q/3+z(s+d)/4,
    theta=(dq/d-dq/s)/12=phi*dC.

The endpoint curve and its literal one-form are

    Zp^2=(H+Cp)^2-4p^6, omega0=dp/Zp.

Write omegaH and omegaC for its literal partial derivatives at fixed C,p
and fixed H,p respectively, before any cohomological reduction. Thus

    omegaH=-(H+Cp)dp/Zp^3,
    omegaC=-(H+Cp)p dp/Zp^3.

The source, with the fiber differential first, is

    S=-omegaH^dH^theta^dz/6.

All current signs below are bound to the ordered top frame
dp wedge dH wedge dq wedge dz.

## Literal first current

The actual coordinate derivatives are

    C_H=z(1/s+1/d)/8,
    C_q=1/3+z[(3q^2-z/4)/s+(-3q^2-z/4)/d]/4,
    theta_H=(1/s^3-1/d^3)dq/24.

In particular the coordinate conversion has a rational product

    C_H*theta=z*q^3*dq/(24*s^2*d^2).

Set

    J0=+omega0^theta^dz/6.

Direct exterior differentiation, using the complete physical derivative
omega0_H=omegaH+C_H*omegaC, gives

    S=dJ0+[z*q^3*omegaC/(144*s^2*d^2)
             +(1/s^3-1/d^3)*omega0/144]^dH^dq^dz.

The rational omegaC term is required. It is not removed by the elliptic
source split.

## Exact elliptic reduction and the second current

Put D=H-1-z^6=-K0 and B=-z/2. For A=+2 and A=-2 define

    E_A=27*A*D^2+4*B^3,
    m0_A=-9*A*D/(2*E_A), m1_A=-3*A*B/E_A,
    R_A=(6*A*B*q^2-9*A*D*q+4*B^2)/E_A.

These are the first H-column and its exact primitive from the full
background elliptic connection. With y_A^2=Aq^3+Bq+D,

    partial_H(dq/y_A)
      =(m0_A+m1_A*q)dq/y_A+d_q(R_A/y_A).

Use subscripts +,- for A=+2,-2, and put

    tau=(R_-/d-R_+/s)/12,
    thetaH_cohom=[(m0_-+m1_-q)/d-(m0_++m1_+q)/s]*dq/12.

Then theta_H=thetaH_cohom+d_q(tau). The actual q-current is

    Jtau=+tau*omega0^dH^dz/6.

The remaining source is exactly

    S-d(J0+Jtau)
      =[(C_H*theta-tau*C_q)*omegaC
          +thetaH_cohom*omega0]^dH^dz/6.

Here theta and thetaH_cohom include their dq differential. When writing
coefficients in dp wedge dH wedge dq wedge dz, use their dq coefficients.
The term -tau*C_q is mandatory: integration by parts differentiates the
actual endpoint kernel along q. Dropping it gives the wrong source.

This coefficient contains the nonzero cross-character term

    -z[R_-*(3q^2-z/4)-R_+*(-3q^2-z/4)]/(48*s*d).

It lies on the background third quotient

    w=s*d, w^2=(K0+zq/2)^2-4q^6.

Thus the two elliptic characters alone do not form a closed source
subsystem after the endpoint C coupling is differentiated. The source-aware
canonical reduction of this term, including its background omega2 infinity
component, is being developed in `coupled-fresh/rank4-relative` by the
relative-cohomology agent. No cancellation of that component is presumed.

## Full two-translation geometry

To differentiate translations, first work on the full product

    E+: s^2=2qplus^3-z*qplus/2-K0,
    E-: d^2=-2qminus^3-z*qminus/2-K0,
    eta+=dqplus/s, eta-=dqminus/d.

Its commuting translation fields are

    D+=s partial_qplus+(3qplus^2-z/4)partial_s,
    D-=d partial_qminus+(-3qminus^2-z/4)partial_d,
    W=D++D-, Wprime=D+-D-.

Let Q=(qplus+qminus)/2, delta=qplus-qminus,
a=(s+d)/2 and b=(s-d)/2. The complete equations are

    W(Q)=a, W(delta)=2b,
    W(a)=3Qdelta-z/4, W(b)=3Q^2+3delta^2/4,
    Wprime(Q)=b, Wprime(delta)=2a,
    Wprime(a)=3Q^2+3delta^2/4,
    Wprime(b)=3Qdelta-z/4.

Extend the actual coupling off the diagonal by

    Cext=Q/3+za/2.

Then

    W(Cext)=a/3+(3z/2)Qdelta-z^2/8,
    Wprime(Cext)=b/3+(3z/2)Q^2+(3z/8)delta^2.

On delta=0, a=x^3,b=y^3. The relative area eta+^eta- is preserved by
both translations, and

    (i_W(eta+^eta-))|delta=0=eta--eta+=12theta,
    W(delta)|delta=0=2y^3.

These bind the translation normal velocity to the exact target density.
They do not make the endpoint coupling constant. In particular,

    [W^2(Cext)]|delta=0=-z/12+3zq*y^3,

whereas differentiating only the restricted first correction
a/3-z^2/8 would lose the second term. Wprime^2 has the same full diagonal
second jet. Both product translations commute before restriction.

The fixed-H,z identities

    q^2 eta+=ds/3+(z/12)eta+,
    q^2 eta-=-dd/3-(z/12)eta-

retain their exact fiber derivatives. Multiplying those primitives by the
endpoint kernel again produces omegaC corrections. The absolute H,z
derivatives use the complete background elliptic connection and its exact
primitives, stored in
`../../../coupled-fresh/infinity-horizontal/background-elliptic-connection.json`.
Relative area invariance alone does not justify dropping those derivatives.

`first_prym_current.py` passes seventeen exact checks of the literal source
current, physical C derivatives, both elliptic Dwork columns, integration
by parts, full off-diagonal translations and the second-jet defect.
The independent audit
`../../../audit/cubic-ray/Prym/PRODUCT-TRANSLATION-AUDIT.md` passed thirty-five
exact Fraction groups and confirmed the current signs and nonzero third
quotient term. The rational omegaC forcing and all elliptic/background
genus-two terms still require an actual coupled correction.
