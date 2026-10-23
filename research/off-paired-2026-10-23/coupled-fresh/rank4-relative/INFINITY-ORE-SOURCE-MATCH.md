# Exact compact-source matching through the infinity derivative

This gives an explicit algebraic source match with one remaining genuine
horizontal residue obligation. That obligation is not discarded. No primitive
or certificate is supplied.

Use the complete compact cyclic notation from
`SCALAR-HORIZONTAL-CLOSURE.md`, including actual physical derivations. Let
omega2=p^2 dp/Z. Its residues at the two infinities are constant and nonzero.
Its two parameter derivatives are compact, with columns cH,cC in
`endpoint/third-kind-connection.json`, and

    cH=e cC,  e=−2C/(3H).

Write cC=sum_j m_j s_j. Exactly,

    m0=2C^3/(567H^2),
    m1=46C^4/(2835H^2),
    m2=(20C^6+2187H^4)/(1890CH^2),
    m3=Delta/(2835H^2),  Delta=4C^6−729H^4.

Define M=sum_j m_j D_C^j and K=M*, so

    K(xi)=sum_j (−D_C)^j(m_j xi).

An infinity current b=(bH,bC,bz) adds compact forcing
`(bC+e bH)cC`; cancellation of its noncompact residue requires
`D_H bH+D_C bC+D_z bz=0`.

## Exact Ore identity

Let L be the monic scalar compact Picard–Fuchs operator. Define

    Uop=u0+u1 D_C+u2 D_C^2,
    u0=−(54328C^12−3197394C^6H^4+98316585H^8)/(1786050C^2H^4),
    u1=−Delta(4652C^6+158193H^4)/(3572100CH^4),
    u2=−23Delta^2/(1786050H^4),

    Vop=v0+v1 D_C+v2 D_C^2+v3 D_C^3,
    v0=613C^3/(63H^2),
    v1=1217C^4/(126H^2),
    v2=(484C^6+12393H^4)/(210CH^2),
    v3=23Delta/(630H^2).

Then the exact noncommutative operator identity is

    Uop L+Vop M=1.

Taking formal adjoints in D_C gives

    L* Uop*+K Vop*=1.

Therefore, for the actual correction forcing sigma=phi_H/6, set

    f=−Uop*(sigma),
    xi=Vop*(sigma).

These explicit rational functions satisfy

    −L*f+K xi=sigma

identically, with all actual a derivatives retained. They match the compact
source before the infinity residue constraint is imposed.

## The remaining horizontal construction

A sufficient constructive realization of xi with zero infinity residue is

    xi=D_z P−T Q,
    T=D_H+(2C/(3H))D_C,

with rational P,Q. Then the genuine three-direction infinity current is

    bH=D_C Q,
    bC=D_z P−D_H Q,
    bz=−D_C P.

Its divergence is zero identically and bC+e bH=xi. This curl realization is
sufficient; rational closed two-forms with nonzero de Rham classes may enlarge
it. No rational P,Q completing the actual xi has yet been obtained.

Once such P,Q are found, put n=m xi and use the triangular compact operator

    Btri(n)=(n1−D_C n2+D_C^2 n3, n2−D_C n3, n3, 0).

The compact C-current is `v(f)−Btri(n)`, where v(f) is the explicit adjoint
current in the scalar closure file. Add the original initial H-current
`−phi s0/6`. Together with b omega2, every compact row then has the original
source and the infinity residue is zero. The stored Dwork primitives for both
the compact and infinity columns give the literal rational correction; no
second-kind component is omitted.

## Source-specific horizontal simplification

Write B=Vop*, theta=C D_C. Then

    B=−C^3/(630H^2)(2theta+3)(46theta^2−105theta+70)
      +729H^2/(630C^3)(theta−2)(theta−1)(23theta+51).

B commutes with T. Consequently the actual source gives

    xi=T(B phi/6)−B theta(phi)/(9H).

The first term has the explicit horizontal potential `Q=−B phi/6`.
The remaining term, including all normal Jacobian derivatives, remains.

For the normal logarithmic coefficient k=(81/2)C^2z, one has exactly

    B theta(k)=−(308/315)(C^3/H^2)k.

Thus its coefficient is a flat-kappa multiple of the original C^2z residue,
where kappa=C^3/H^2 and T(kappa)=D_z(kappa)=0. This does not mean the complete
normal logarithmic term has vanished.

A useful actual rational curl completion uses l=dlog(a), the closed rational
one-form, and g=C^2z^2/2:

    P=g T(log a),  Q=g D_z(log a),
    D_z P−T Q
      =C^2z T(log a)−(2C^2z^2/(3H))D_z(log a).

The displayed derivatives of log(a) mean a_i/a and are rational. No logarithm
is used as a certificate coefficient. The additional D_z(log a) term must
still be matched; this is a source-derived partial curl, not a solve.

`verify_infinity_ore_general.py` checks the complete general-H Ore identity,
homogeneity, the Euler factorization of B, and the logarithmic-coefficient
identity exactly. `infinity-ore-general.json` stores all operator coefficients.
