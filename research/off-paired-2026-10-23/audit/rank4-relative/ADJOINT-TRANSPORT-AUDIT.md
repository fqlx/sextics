# Independent audit of physical adjoint transport

The mechanism in `coupled-fresh/rank4-relative/ADJOINT-TRANSPORT.md` is valid.
It supplies the stated finite horizontal correction for any proposed scalar
potential. It does not supply a potential solving the forcing equation.

`verify_adjoint_transport_fraction.py` passes 22 independent exact groups
using standard-library Fraction polynomial arithmetic. The proof is generic
in `H,H_a,H_C,H_aa,H_aC,H_CC`, with all identities reduced modulo
`tau^3-H`. It imports neither the primary transport verifier nor SymPy.
The note hash is recorded in `adjoint-transport-fraction-results.json`.

## Physical derivations and volume

Write `h=partial_C H|a,z`, `A=H_a`, `k=2C/(3H)` and `r=1-kh`. In the bare
`(a,C,z)` coordinates, the two physical derivations have components

    T=(r/A) partial_a+k partial_C,
    B=-(tau^2 h/A) partial_a+tau^2 partial_C.

Every bare derivative also differentiates `tau^3=H`. In particular

    T(H)=1, B(H)=0,
    T(tau)=tau/(3H), B(tau)=0,
    T(b)=0, B(b)=1, b=C/tau^2.

The independent calculation checks their full commutator, including the root
variable. The physical finite-coordinate relation previously audited gives
`H_a=P_a/a^2` and `h=P_C/a^2` on `P=0`; it does not set either physical
coefficient derivative of `a` to zero.

The volume is exactly

    mu=H^(-2/3) dH wedge dC wedge dz
      =rho da wedge dC wedge dz,
    rho=H_a/tau^2.

This is the pullback volume on the finite root cover, with no covering-degree
factor inserted into a differential pullback. In `(tau,b,z)` it is
`3 tau^2 d tau wedge db wedge dz`, which also directly shows that `B` and
`T` have zero divergence. In the original `(x,y,z)` chart,

    H^(-2/3) J T=(b_y,-b_x,0),

because `b_i=H^(-2/3)(C_i-k H_i)`. This confirms the same physical volume
and orientation independently of the bare chart.

## First-order identity and all fourth-order corrections

With `beta=tau^2/r`, the exact vector identity is

    B=beta delta-beta h T.

The independent audit checks both its derivative coefficients and the entire
zero-order term in

    B(F)=rho^(-1) delta(rho beta F)-T(beta h F).

Indeed zero divergence of both vector fields implies

    delta(rho beta)=rho T(beta h),

which is exactly the product-rule term needed here. Retaining only
`beta delta F` would be wrong.

Put `Dcal(F)=rho^(-1)delta(rho beta F)` and `m=beta h`. The finite correction
can equivalently be written

    K_n(F)=sum_(j=0)^(n-1) B^j(m Dcal^(n-1-j)F).

The noncommutative telescoping identity for `B^n-Dcal^n`, together with
`[B,T]=0`, gives

    B^n(F)=Dcal^n(F)-T K_n(F).

This proof does not require `Dcal` to commute with `T` and includes every
derivative of `beta h` in the recurrence. Applying it separately to `F`,
`c3 F`, `c2 F` and `c1 F` proves the primary fourth-order `J(F)` formula.
It is a finite exact construction, rather than an unverified truncation.

The coefficient weights check exactly as

    c_j(H,C)=tau^(2j-8)c_j(1,b).

Since `D_C=tau^(-2)B` and `D_C(tau)=0`, every ordered term in the adjoint
therefore gives

    L*(tau^8 F)=L_b*F=Lcal*F-T J(F).

The source reconstruction sign follows without convention choices:

    -L*(tau^8 F)+T U
      =-Lcal*F+T(J(F)+U).

Thus an identity with horizontal function `U_tilde` uses
`U=U_tilde-J(F)`, as stated.

## Monic potential and adjunction

Let `Aop=beta delta`. Its formal adjoint for `mu=rho da dC dz` is

    Aop^dagger=-rho^(-1)delta rho beta=-Dcal.

Consequently `L_b(Aop)^dagger=Lcal*`, with coefficient multiplication in
the order displayed in the primary note. The ordinary delta-adjoint and
the rho-adjoint are related by `M^dagger=rho^(-1)M* rho`.
For `L_delta=beta^(-4)L_b(Aop)`, adjunction reverses the left scalar factor:

    L_delta*=L_b(Aop)* beta^(-4),
    L_delta*G=rho Lcal*(G/(rho beta^4)).

This proves the asserted potential convention and its exact physical factor:

    F=G/(rho beta^4),
    f=tau^8 F=tau^2 r^4 a^2 G/P_a.

The last equality is also checked by polynomial clearing. In one dimension,
`rho=1/beta` gives `F=beta^(-3)G`, consistent with the cubic transformation
law for the last fourth-order cyclic current coefficient.

The complete monic bare-section equation is, precisely,

    -L_delta*G+rho T(U_tilde)+rho D_z W=rho sigma.

One must retain these horizontal terms when using the statement that the
forcing becomes `rho sigma`. Replacing `rho T(U_tilde)` by
`T(rho U_tilde)` introduces an additional derivative term. Likewise `D_z`
continues to mean the original physical derivative at fixed `H,C`:
in a bare chart it includes `-H_z/H_a` times the bare a derivative.

## Descent and remaining obligation

The root cover has characteristic zero and finite degree three. A genuine
source-carrying full current on it can be descended by normalized field trace,
which commutes with the uniquely extended derivations. An arbitrary scalar
trial does not by itself give such a current. The full compact reconstruction,
exact fiber corrections, homogeneous legal denominator clearing and final
original-target verification remain necessary.

The bare exponents of the suggested `R/C^3` trial do not remove the `rho`
and `beta` drift or the transformed lower coefficients. This audit makes no
claim that the trial satisfies the forcing. No certificate has been found.
