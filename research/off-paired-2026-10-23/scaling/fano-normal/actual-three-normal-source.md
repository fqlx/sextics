# The actual source on a Fano/Cardano incidence

No primitive is established here. These identities specify the source and
the extra normal corrections for a prospective two-companion construction.

Use the actual affine cubic-ray variables `q=(x,a,u,v)` and
`H=1+x^6+a^6`, `C=1+u^6+v^6`, with the complete physical coupling `B`.
Introduce variables `(S,T,c)` and the three equations

\[
 G_1=S^3+T^3-H,\qquad G_2=c^3-C,\qquad
 Q=B+3cST.
\]

On this incidence the physical cubic root is `p=-(S+T)/c`. Thus
`H+Bp+Cp³=0` identically, and no mixed coefficient is removed.
Let

\[
 K=S^2+ST+T^2,\qquad \delta=S^3-T^3.
\]

The exact normal Jacobian and actual residue scalar are

\[
 J=\det\frac{\partial(G_1,G_2,Q)}{\partial(S,T,c)}
 =-27c^3\delta,
\]
\[
 g=3cK,\qquad R=\frac{ST(S+T)}{9c^3K^3}.
\]

Consequently, with the normal order `(G1,G2,Q)` and ambient order
`(x,a,u,v,S,T,c)`, the original four-form `R dq` is the three-normal
residue of

\[
 \frac{N\,dq\wedge dS\wedge dT\wedge dc}{G_1G_2Q},
 \qquad N=-\frac{3ST(S^2-T^2)}{K^2}=JR.
\]

## All physical horizontal derivatives

For any base derivative `partial_i`, the derivatives on the incidence are

\[
 c_i=\frac{C_i}{3c^2},\qquad
 U_i=-\frac{B_i}{3c}-\frac{STC_i}{3c^3},
\]
\[
 S_i=\frac{SH_i/3-T^2U_i}{\delta},\qquad
 T_i=\frac{S^2U_i-TH_i/3}{\delta}.
\]

They satisfy all three differentiated normal equations. In particular,
the `B_i` and `c_i ST` terms are part of the physical derivative.

## First exact elliptic primitive and its normal correction

The first Fano companion is
`W_H: S³+T³=H(X)` in `P(1,1,1,2,2)`. On it the vertical elliptic field

\[
 \delta_E=3T^2\partial_S-3S^2\partial_T
\]

preserves `H`, and for `qE=-(S+T)/(2K)` one has

\[
 \delta_Eq_E=N,\qquad \delta_EQ=-9c\delta.
\]

Because `deltaE(G2)=0`, the exact identity of rational functions is

\[
 \frac{N}{G_2Q}=
 \delta_E\left(\frac{q_E}{G_2Q}\right)
 +\frac{q_E\delta_EQ}{G_2Q^2}.
\]

The double-`Q` correction must be retained. As `Q_c=3ST`, its scalar
normal residue is explicitly

\[
 \frac1{3ST}\partial_c
 \left(\frac{q_E\delta_EQ}{3STG_2}\right)
 =\frac{q_E\delta(2c^3+C)}{S^2T^2G_2^2},
 \qquad c=-\frac B{3ST}.
\]

This displayed scalar uses the normal derivative operator with `Q`
first; the wedge sign changes when interchanging the normal order
`(Q,G2)` and `(G2,Q)`.

## The actual second moving ternary sextic

Set `t=ST` and eliminate `c` in `Q`. The remaining ternary sextic is

\[
 G_{\rm eff}(Y)=F_Y(Y)+\frac{B_X(Y)^3}{27t^3}.
\]

It retains the entire quadratic form `B_X(Y)`. The second-normal scalar
has pole order two on this sextic, with numerator proportional to

\[
 F_Y-\frac{2B_X^3}{27t^3}.
\]

For projective plane volume, the affine `Y0=1` representative is
homogenized by multiplying that degree-six numerator by `Y0³`, giving
degree nine as required for a pole-two plane form.

The numerator is a specific parameter derivative:

\[
 \frac{F_Y-2D}{(F_Y+D)^2}
 =-t^2\partial_t\left(\frac1{t(F_Y+D)}\right),
 \qquad D=\frac{B_X^3}{27t^3}.
\]

Here `X,Y` are held fixed. This is useful input to a jet-compatible
companion theorem; it does not cancel the derivative of a primitive
whose coefficients also depend on `t`.

## An actual relative Fano complete intersection

Over `W_H` on `ST != 0`, consider

\[
 Q=B_X(Y)+3STc=0,\qquad
 J_Y=F_Y(Y)-c^3-d^3-e^3=0
\]

inside `P(1,1,1,2,2,2)` with coordinates `(Y0,Y1,Y2,c,d,e)`.
Its dimension is three and weighted adjunction gives `-K=O(1)`:
the weights sum to nine and the degrees sum to eight. Eliminating `c`
identifies it with the standard companion
`d³+e³=G_eff(Y)`. Generic quasismoothness follows on the open smooth
sextic locus; this locus is nonempty, for example at `X1=0,S=T=1,H=2`,
where `B=0` and the moving sextic is Fermat.

The original physical curve has `d=e=0`, a codimension-two boundary.
The divisor `d³+e³=0` still contains an extra weighted line parameter.
One exact way to retain the required physical boundary density is the
three-normal residue in `(JY,d,e)` of

\[
 \frac{P_2\,du\wedge dv\wedge dd\wedge de}{J_Y^2de},
\]

where `P2` is the actual pole-two numerator above. At `d=e=0` this is
the normal residue of `P2 du dv/G_eff²`. The poles in `d,e` are part of
the construction. Neither the Fano property nor an arbitrary-density
integration statement removes them or the parameter derivatives.

A complete solution must construct the scalar primitive for this exact
source with its boundary poles and mixed parameter jets, or supply an
equivalent physical current. The checker `verify_three_normals.py`
verifies thirteen exact normal/source identities.

Prepared with OpenAI Codex assistance.
