# A rational three-form current and a single holomorphic plane-sextic residual

Use the final tensor in EXACT_EULER_REDUCTION.md. Choose its rational
representative in the order dI∧dJ∧dτ∧db. The genus-four equation is
f_C=y⁶+1+Jτ³+y(Iτ²+τ)/2. At fixed τ and I, the lift of ∂J sends
y to −τ³/f_C,y. Applied twice to 1/f_C,y it gives
τ⁶(3f_C,yy²−f_C,y f_C,yyy)/f_C,y⁵. The genus-ten factor is
(I²b⁴T/6+2Ib⁸)db/P_T. Eliminating J as the rational function
T+(1+b³)/T+I/(2b)+I⁶T³/b⁹ gives J_T=P_T/(b⁹T) on P=0.
Thus the remaining absolute four-form in fibre-first orientation is

    Ω=−τ⁶/12 · (I²/(6b⁵)+2I/(bT))
              (3f_C,yy²−f_C,y f_C,yyy)/f_C,y⁵ · dI∧dτ∧db∧dT.

The previous reductions supply rational currents relating this representative
to the original target.

## Switching to a curve over three independent parameters

Keep τ,b,T as independent parameters. Set X=τI, Y=b y/τ, m=τ²/(2b).
Then f_C=m F where

    F=AY⁶+BX⁶+XY+X+Y+C,
    A=2τ⁴/b⁵,    B=2T³/(τ⁵b⁸),    C=2b/τ²+2τb(T+(1+b³)/T).

The generic projective plane sextic is smooth. At infinity smoothness follows
from AB≠0. In the affine chart the two partials have finitely many simultaneous
zeroes over the algebraic closure of ℂ(A,B), because substituting Y=−1−6BX⁵
in F_Y gives a degree-25 equation. C is an independent transcendental, as can
also be seen from the explicit finite cover below, so these critical points
miss the generic level. Adjunction gives genus 10 and shows that X^i dX/F_Y
is holomorphic for i=0,1,2.

Write ν=dlogτ∧dlogb∧dlogT and ρ=1/F_Y. A tangent lift in all that follows
keeps X fixed. Let

    V=5τ∂τ+4b∂b+19T∂T,  E=VC,  S=V/E,
    U=−b∂b−3T∂T,        r=6τb(T−1/T)/E,  L=U+rV.

Then (SA,SB,SC)=(0,0,1) and (LA,LB,LC)=(5A,−B,−C). E is nonzero
(e.g. E=28 at τ=b=T=1). The lifts to F=0 act by

    S̃Y=−ρ,    L̃Y=−Y−Xρ,    S̃X=L̃X=0.

Since f_C,y=(τ/2)F_Y, switching volume to dX∧ν gives

    Ω=−[g₂ S̃²(X²ρ)+g₁ S̃²(Xρ)] dX∧ν/12,
    g₂=4T/(3τb²),   g₁=16b².

In fact S̃(X^{i+1}ρ)=L̃(X^iρ) for every i. This is literal:
on F=0, X−L(F)=−Y F_Y and L(F_Y)=Y F_YY, where L here
denotes parameter-only differentiation. The two terms in differentiating
1/F_Y cancel. Moreover [S̃,L̃]=−S̃ as checked on A,B,C,X,Y.
It follows that S̃²(X²ρ)=(L̃−1)L̃ρ, and S̃²(Xρ)=(L̃−1)S̃ρ.

## A rational current

For a base vector D use D*g=−div_ν(g D) and write ι_Dν for contraction.
Set

    H₂=(L*−1)g₂,   H₁=(L*−1)g₁,   h=L*H₂+S*H₁,
    K=(1/12)dX∧[(g₂L̃ρ+g₁S̃ρ+H₂ρ)ι_Lν + H₁ρ ι_Sν].

These are rational forms on the original four-dimensional function field.
For any rational function q,
d(q dX∧ι_Dν)=−(D̃q+q div_ν D)dX∧ν. Applying this identity to the four
terms proves the full rational identity

    Ω − dK = −h (dX/F_Y)∧ν /12.

For convenient exact evaluation,

    h=V[U(rg₂)+rV(rg₂)−(g₁−V(rg₁))/E].

At τ=b=T=1 it equals −3336/7. Over the generic base the remaining
relative one-form is thus a nonzero holomorphic form on the complete
plane sextic. A rational primitive of this absolute residual would finish
the direct route. Its restriction as a relative curve differential has
no rational function primitive, since an exact holomorphic differential
on a smooth proper curve in characteristic zero vanishes. Base
derivatives and additional supports are available in the absolute problem.

## The common level and its algebraic sheets

The monomial parameters a=τ⁴/b⁵, d=τT/b⁶, z=τ/b are birational,
with inverse τ=z⁵/a, b=z⁴/a, T=d z¹⁹/a⁵. The equation and both
source coefficients only involve s=z²:

    A=2a, B=2d³/a²,
    C(s)=2a/s³+2d s¹⁴/a⁷+2a³/(d s⁵)+2s/d,
    g₂=4d s³/(3a²),  g₁=16s⁴/a².

The level projection from s to C has degree 19 with poles of orders 5 and
14. Its trace annihilates the two forcing densities after converting ds/s to
dC. In fact for k=3,4 and P(s)=s⁵(C(s)−C), the trace of s^{k−1}/C'(s)
is the sum of s_j^{k+4}/P'(s_j) over the nineteen generic roots, zero by
Lagrange interpolation since k+4<18. Covariant differentiation commutes
with this finite trace. This only describes the projection to the base
field. The trace-zero part on the actual algebraic sheets remains.

## Reproduction

Run rational_current.py with Python and SymPy for exact implementation
checks of the equation, coordinates, actual Jacobians, orientation,
both derivative transports, commutator, and finite cover.
one_scalar.py checks the displayed value of h by an independent exact
calculation. Prepared with OpenAI ChatGPT assistance.
