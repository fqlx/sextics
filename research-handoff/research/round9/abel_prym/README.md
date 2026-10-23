# Marked-point Abel–Prym channel for cyclic-triple-residual

This is a constructive scratch channel, not a certificate. The exact source is bound in `../cyclic_full/independent_physical_source.json` and `/workspace/research/round8/coupled_source/README.md`.

The constant sextic is

    Gamma: w^6 + c*w^3 + 1 + v^6 = 0, c=5/7.

The point `P=(W=w/rho,h=1,T=z)`, with `rho^3=M` and `z=BR/A`, lies on the canonical cyclic curve. The divisor `P-sigma(P)`, `sigma(W)=zeta3*W`, has norm zero to the elliptic quotient. Its differential along the rational canonical isoperiodic flow is nonzero at three good points modulo1009 (`marked_point_probe.py/json`). Its characteristic-zero algebraic definition and the exact Gauss–Manin primitive convention make this a test of nonidentity, not a source match.

The absolute lift uses the **plus** primitive

    beta_abs = beta + sum_j [(QW-W*Qh)/C_t] dz_j.

This was independently audited by certificate_search, including108 direct differentiation/residue checks and the universal weighted-divergence identity. Receipt: `/workspace/research/round9/coupled_search/absolute_lift_audit.json`. Reflection is independently auditing the marked-flow and trace conventions.

A critical scope limitation: `T=z` maps to `t_old=0`. The direct marked divisor is birational to `Gamma x A^2`, and its proper smooth model has `H^{2,0}=0`. Its direct Gysin cannot serve the target. Any serving construction must use a different spread, correspondence, or rational-current channel. The actual source numerator nevertheless equals `alpha^2*h^4*(T-z*h^2)^2`, so its double zero at the marked point gives a concrete jet comparison.

## Exact quadratic trace simplification

`closed_trace.py/json/pickle` independently proves a useful rational trace formula for the11 base2form generators, without expanding the physical parameter map. Put

    u=w^3, u^2+c*u+P=0, P=1+v^6,
    E=1+a*v, Ct=(c/M)*(u+a*v/E).

If `H=A1+B1*u` and `Ct=aa+bb*u`, then

    Tr_u[H/((2u+c)*Ct)] = (aa*B1-bb*A1)/N,
    N=aa^2-aa*bb*c+bb^2*P.

Multiplication by `u` changes the numerator to

    aa*A1+(bb*P-aa*c)*B1.

Thus the Gamma branch factor cancels. Exactly,

    N = c^2*G/(M^2*E^2),
    G = (1+v^6)*E^2 - c*a*v*E + a^2*v^2.

The earlier tentative simplification `G=P*E^2-av` was wrong for `c=5/7` and has been withdrawn; the exact script verifies the corrected formula. The degree10 physical homogeneous form is

    (X0^6+X1^6)*(X0*Y2+X1*Y0)^2
    -c*X0^6*X1*Y0*(X0*Y2+X1*Y0)
    +X0^6*X1^2*Y0^2.

For an actual holomorphic marked form, write

    rho*alpha_i = w*[n_i*(dlogw-dlogM/3)+sum H_ij dz_j]/Ct,
    n=(1,z), H_ij=(QW-W*Qh)/W.

Pairing with Gamma's opposite-character holomorphic forms `w*v^j*dv/Fw`, `j=0..2`, kills `dlogw` by the wedge with `dv`. The unnormalized degree6 trace is

    v^j * [ n_i*bb/(3N)*dlogM
            +sum (aa*B_ij-bb*A_ij)/N dz_j ] wedge dv.

Here `H_ij=A_ij+B_ij*u` exactly; no higher u power occurs in the pinned primitive data. Conjugate marked forms use `rho^2*alpha`, Gamma numerators `v^j`, `j=0..3`, or `w^3`, giving five more generators. `closed_trace.pickle` contains the nine exact `(A_ij,B_ij)` pairs and the rules. Certificate_search owns the full-current divergence/source comparison; these trace identities do not themselves assert a primitive.

## Separate fixed cubic support filter

The noncoordinate ramification factor

    D=2X2^3+c*(X0^3+X0*Y1*Y2+X1*Y0*Y1)

satisfies the literal identity `F_X2=3X2^2D` for the pinned instance. `ramification/e1.py/json` proves `A*D` is not in the Jacobian ideal: degree9 coefficient matrix2002x756 has rank756 modulo1000003, while its augmented matrix has rank757. A nonzero augmented757-minor modulo a good prime proves characteristic-zero nonmembership since the coefficient matrix has only756 columns. Therefore this prescribed reduced support and all its powers fail q1. No conclusion about unions or general certificates is drawn.

## Source-specific replacement section

The source doublezero at the original marked point does not give that point's single Schiffer channel. Rank's exact audit `/workspace/research/round9/cyclic_full/schiffer_audit.json` proves

    eta[h²*(T-z*h²)^3] != 0

at three characteristic-zero physical points. Let `S0=h4*(T-z*h²)^2`, `S1=h²*T*(T-z*h²)^2`, and write `eta(Si)=Ni/D` in a common denominator. `effective_schiffer.py/json/pickle` constructs

    T_eff=N1/N0,
    D_eff=N0*T-N1*h²,
    h²*D_eff*(T-z*h²)^2 = sum_i Q_i*C_i.

All `Q_i` are polynomial in the canonical parameters and fiber variables; the equality is verified coefficientwise over QQ. N0/N1 have32/35 terms. This is a source-specific **weight8 Higgs identity**. It is stronger than merely multiplying a weight8 source by an arbitrary weight2 graph and reducing in weight10, which can be automatic. It is not a physical certificate.

`effective_physical.py/json/pickle` pulls this section back exactly with native rational polynomial arithmetic. After cancellation, old `t/h²` has248/310 numerator/denominator terms. `effective_graph.py/json/pickle` exports the resulting primitive homogeneous support: degree32,558 terms, integer coefficients with at most10 digits. Homogenization removes a common `X0²Y2²` from the naive degree36 expression. A physical vector-field lift must retain the `Y2` poles from

    partial_t_old=(a*partial_Y0+b*partial_Y1+partial_Y2)/(2*y)

and all base derivatives. Neither a legal E2 solution nor a holomorphic2form/Gysin binding has been found.

## G fixed-part check

`G_KS.py/json` tests the b-direction on the normalized G support. Both eigenblocks have nonzero hol-to-eta coefficients at four good finite-prime points, so the full Prym is not b-isotrivial. More precisely, `G_fixed_part.py/json` tests the unique actual holomorphic Higgs-kernel line

    h=(N_b[1,2],-N_b[0,2],0).

The wedge `h wedge (partial_b h+N_b^T h)` is nonzero at all four points. The conjugate holomorphic line already has nonzero Higgs. Therefore a constant CM E0 summand is excluded along generic b on G. Reflection independently replayed all jets, connection entries, smoothness/unit checks, and wedges in `independent_G_fixed_part.py/json`. This does not exclude all holomorphic2forms or all source-current routes on G.
