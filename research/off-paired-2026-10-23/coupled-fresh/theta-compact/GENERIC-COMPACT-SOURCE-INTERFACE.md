# Generic compact source interface and finite w-presentation

This work does **not** give a primitive or certificate. The original source is
still open. It supplies an exact generic curve connection, complete source
arrays, and explicit next horizontal moments. No Lean, kernel, CI or acceptance
claim follows from these calculations.

## The generic affine and compact bases

On

    ab=q³, Q=a²+b²+cq²+daq+eq+1=0,
    J=2a²+daq−2b²,

write df=δf dq/J. The exact polynomial derivation is

    δq=J,
    δa=−a(2cq+da+e)−6bq²,
    δb=b(2cq+da+e)+3q²(2a+dq).

The affine cohomology basis is

    [1,q,q²,q³,q⁴,a,aq,b,bq] dq/J.

Ten exact functions of pole weight at most seven complement these nine forms
inside all nineteen numerator words of weight at most eleven. The reduction
matrix has the constant determinant 3251404800. The exact ΩΘ reduction is in
`affine-theta-reduction-results.json`.

Put Cp=c−d²/4 and r=Cp(Cp−d²)/8. The eight compact forms are

    [1,q,q³,q⁴−r q²,a,aq+(d/2)q²,b,bq] dq/J.

The omitted ninth class is ω=q²dq/J. The infinity residue ratios are
res(aq/J)/res(ω)=−d/2 and res(q⁴/J)/res(ω)=r. The ΩΘ coefficient has zero
ninth residue component identically.

## Full generic connection

Parameter differentiation is reduced by

    ∂p(N dq/J)=ΣΓp[row,N] basis_row+d_q(f_N/J).

The 37×25 polynomial matrix uses sixteen nonredundant f words of weight at
most ten and the nine affine basis forms. Its selected 25×25 minor is a
nonzero constant times d² times the degree-four-in-v discriminant. A native
FLINT Bareiss calculation after seventeen constant pivots solves an eight by
eight core. All 333 generic cleared polynomial identities for
V=2c∂c+d∂d+e∂e pass. The arrays, including every exact fiber primitive, are
`affine-V-generic-results.json`; rerun with `finalize_generic_flint.py`.

For i=c/e², j=d/e, v=e⁶, the descended curve is

    ay=x³,
    y²+v(a²+i x²+jax+x+1)=0,
    Jbar=2va²+jvax−2y².

The compact basis is deck-gauged by e to powers [1,2,4,5,1,2,4,5]. Its exact
connection is in `rank8-descended-connection-results.json`, with
Γw=v_w ΓV/(6v). Columns differentiate basis forms. Thus current coefficient
vectors satisfy P_w+Γw P=S. Independent audit of all full connection and
flatness identities is recorded in `../../audit/theta/`.

The local exponents are in `connection-native-local-results.json`. At v=0
they are 1/6,1/3,2/3,5/6, each twice. Every finite discriminant residue squares
to zero. The diagonal infinity shear v^[1,1,0,0,1,1,0,0] gives exponents
−1 six times, −1/2 and −3/2. The full-base i,j connections and literal fiber
primitives live in `../ruling-source/full-base-connection/`.

## Actual source and its finite w-presentation

Use the independently audited full-base Euler current. Its actual remaining
source, for volume di dj dw, is

    S = a0/6 (4 e_b−ΓD e_b),
    ΓD=ΓV−2iΓi−jΓj,
    a0=54 i³w(1+w³)/(j²N),
    N=9i²w²−16j²(1+w³).

Here e_b has index six in the eight compact rows. This is a source-carrying
formula, not universal polynomial-density integration. The scalar K and both
third-kind source rows were removed by explicit full-base currents.

`source-leray-presentation-results.json` records the full actual source class
after an explicit polynomial infinity current Pinf=w²p2+wp1. Put T=1+w³,

    L=256T⁵N+729i⁶j²w⁶,
    A=64j²wNT², B=9i²L, v=A/B,
    Dc=B⁴D(A/B),
    s=[1,1,0,0,1,1,0,0],
    H_row=wNT Dc L^(1+s_row).

The one-form numerators have degree less than deg(H_row), respectively 115
or 97, giving 848 scalar coordinates over Q(i,j). The zero-form currents are
w^k/L in each of the four s=1 rows, k=0,...,18, and constants in the other four
rows, giving eighty columns. The file gives every actual source numerator
(6.8 MB), the exact factored matrix formula, both known infinity-current
vectors and source hashes. All row degree bounds and all eighty current
column bounds pass.

This is a complete finite logarithmic presentation, not an expanded reduced
768-dimensional cokernel basis. The horizontal action is induced by the
audited flat connection and higher-pole reduction. A full reduced horizontal
connection and a rational horizontal primitive remain to be constructed.
The initial Taylor excess coefficients are merely source projection feedback;
they are not a substitute for solving the full-base source.

## Further literal horizontal moments

Let V0=i x²+x+1. The first two literal j moments are

    Ψ1=x² dx/(2a²),
    Ψ2=[x/(2a)−xV0/(6a³)−3x⁷/(10v a⁵)] dx,
    ∂j Ψ1=ν_b,  ∂j Ψ2=Ψ1.

A third rational moment exists modulo a rational fiber correction, explicitly
in `j-moment-hierarchy-results.json`. Nine exact groups passed in
`verify_j_moment_hierarchy.py`. The density derivatives after repeated
integration by parts remain part of the source. Ψ2 and (2−D)Ψ2 must not be
assumed compact; their finite residue components require retention/audit.

Fresh's separately verified compact current U=(3−D)Ψ1 satisfies
∇j U=(4−ΓD)e_b. Its exact arrays are in
`../ruling-source/full-base-connection/j-source-primitive-results.json`.
The remaining actual source after using this current is −t_j U, with the
full physical density and fixed-v derivative retained.

## Actual horizontal source poles now served

`actual-N-j-removed-source-results.json` supersedes the N-only packet. The
quartic agent's fixed-w j current

    Pj=[−iT/(4wj)+28T²j/(45iw³)] e_bq

serves both the full N source pole and the full j=0 source pole. Twenty-two
exact generic groups pass in `remove_actual_N_j_poles.py`. Full fixed-w
transport Γj+(v_j/(6v))ΓV is retained, and the literal rational fiber primitive
references are included.

The remaining actual eight-vector is recorded as

    R=64iw²T³/L B−cv J−dv H+e e_bq,
    B=(Q+ΓV e_bq/30)/v,
    H=(ΓV e_bq−5e_bq)/v,
    J=Γj e_bq/v.

All three numerator vectors divide by v exactly. Their shared curve
discriminant denominator and all scalar coefficients are in the packet.
There are no N, j or critical-v_w denominators left. The remaining explicit
pole set is i=0, w=0, L=0 and the curve discriminant. Their intersections have
not been served. The quartic agent continues the joint w/j current that
removes the introduced w=0 principal parts while preserving N and j.

`mixed-i-primitive-results.json` gives an additional compact source potential

    Vi=−y²dx/(2x⁵)+(j/2)ζhat,
    ∇i Vi=U1+(j/2)ν_bq.

The finite residues cancel and infinity residues vanish; every finite pole is
removed by an explicit rational fiber primitive before polynomial reduction.
All eight generic matrix rows pass. This lets the actual density correction
−t_j U1 transfer to t_ji Vi+(j/2)t_j ν_bq, with the known i current retained.

Finally, the full discriminant normal identities

    6v D_v Γp_num−D_p ΓV_num ≡0 mod D,  p=i,j

pass all 128 entries. A seven by seven Sylvester calculation constructs a
complete exact inverse of D_i modulo D; its denominator depends only on i,j.
The arrays are `discriminant-normal-residue-results.json` and
`discriminant-normal-inverse-results.json`. These expose a possible normal
current for the actual remaining discriminant source. No such physical
current, including its introduced Piola/fold poles, is claimed in those files.
