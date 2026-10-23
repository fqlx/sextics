# Source-bound rational lift through the (N)-only representative

This constructs the scalar correction (K) for the **actual** rationalized
forcing. It does not serve the retained curve-valued defect and is not a
primitive of the original sextic.

The authoritative source and potential arrays are in
`../../genus4-gm-independent/corrected-rational-source-binding.json` and
`../../genus4-gm-independent/cubic-residue-potentials-results.json`, with
source SHA256
`d725307869fcf3a2f064a0a6616eee78ea59f74dd3305fcb1d2408d3018f25b5`.
The `actual_Ssrc_residue` record is authoritative. The separate `h_residue`
record does not serve the actual differentiated forcing.

Write

\[
u=J/i^2,\quad T=1+w^3,\quad N_0=9w^2-16uT,
\]
\[
L_0=256T^5N_0+729i^6u w^6,
\qquad v=\frac{64u wN_0T^2}{9L_0}.
\]

Let (A=\partial_i|_{J,v}), (B=\partial_J|_{i,v}),

\[
Z=v\partial_v,\qquad D=6Z-2iA-2JB,
\qquad S_{\rm src}=(D-6)(D-5)h.
\]

The rational adjoints are

\[
P_E=(D-6)(D-5)+A(Z+D/2-2),
\]
\[
P_D=4JB^2+2B+A(Z+JB),
\]
\[
P_3=A^3+v(Z+JB+1)Z(Z+D/2+1).
\]

Let (f,g,c_0\in\mathbb Q(u)[w]), each of degree at most two in (w),
be the arrays `PE_residue_f_coefficients`, `PD_residue_g_coefficients`, and
`CRT_factor_coefficients` in the authoritative record. The actual potentials
are

\[
F=\frac{v^2}{v_w}i^{-1}f\frac{(N_0)_w}{N_0},\qquad
G=\frac{v^2}{v_w}g\frac{(N_0)_w}{N_0},
\]
\[
t=i^{-4}wTL_0c_0,\qquad H_{\rm pot}=vt.
\]

The construction below retains their full physical derivatives.

## Literal Cartan corrections

For every rational scalar (F), put

\[
\alpha(F)=F\,dv/v^2=Fv_w/v^2\,dw.
\]

Derivatives on the right below hold (w) fixed. Direct differentiation gives

\[
\alpha(AF)=\partial_i\alpha(F)+d_w E_A(F),\qquad
E_A(F)=-Fv_i/v^2,
\]
\[
\alpha(BF)=\partial_J\alpha(F)+d_w E_B(F),\qquad
E_B(F)=-Fv_J/v^2,
\]
\[
\alpha(ZF)=\alpha(F)+d_w E_Z(F),\qquad E_Z(F)=F/v.
\]

Thus (\bar A=\partial_i), (\bar B=\partial_J), (\bar Z=1), and

\[
\bar D=6-2i\partial_i-2J\partial_J,\qquad
E_D(F)=6F/v+2iFv_i/v^2+2JFv_J/v^2.
\]

For sums and products, keep every correction using

\[
E_{M+N}=E_M+E_N,\qquad
E_{MN}(F)=\bar M E_N(F)+E_M(NF).
\]

Base scalar multiplications have zero correction. These are literal rational
identities, so apparent poles at (v_w=0) have not been omitted.

The exact cubic identity is

\[
P_3(vt)=vA^3t+(Z-1)W,
\qquad W=v^2(Z+JB+2)(Z+D/2+5)t.
\]

Consequently

\[
\alpha(P_3(vt))=\partial_i^3(t\,d\log v)
 +d_w\bigl(E_{A^3}(vt)+W/v\bigr),
\]
\[
E_{A^3}(F)=\partial_i^2E_A(F)+\partial_iE_A(AF)+E_A(A^2F).
\]

The latter formula uses (vA^3t=A^3(vt)), since (Av=0).

## All finite residues, including folds

The initial one-forms are

\[
\alpha(h)=i^{-1}\frac{54wT}{uN_0}\,dw,
\quad \alpha(F)=i^{-1}f\frac{(N_0)_w}{N_0}\,dw,
\quad \alpha(G)=g\frac{(N_0)_w}{N_0}\,dw.
\]

Each has only (N_0=0) as a finite pole. In addition, (t) is polynomial in
(w) and is divisible by (wTL_0). Since

\[
d\log v=\left(1/w+(N_0)_w/N_0+2T_w/T-(L_0)_w/L_0\right)dw,
\]

the one-form (t\,d\log v) also has only (N_0=0) as a finite pole.
Ordinary (i,J) derivatives preserve this support. Every difference from
the full differentiated actual expression is the differential of an
explicit rational scalar above. Such differentials have zero residues at
all points, including the critical points (v_w=0), (w=0), (T=0), and
(L_0=0).

The independently audited **right** Ore identity serves the full actual
(N_0)-residue, with

\[
r_{\rm Target}=2(\theta+1)(2\theta+3)r_h
 =4u^2r_h''+14ur_h'+6r_h,
\quad \theta=u\partial_u
\]

on the cubic field. Therefore all finite residues of the full actual
remainder vanish. Its residue at infinity vanishes by the residue theorem.
This establishes rational integrability over \(\mathbb Q(i,J)(w)\); it is
not an assumption about a selected coefficient matrix.

## An explicit small-denominator representative

For the following formulas only, \(\theta=u\partial_u|_w\). Set

\[
m=(N_0)_w/N_0,\quad a_h=54wT/(uN_0),\quad a_f=fm,\quad a_g=gm,
\]
\[
P_-=256c_0T^5N_0(1-8w^3),
\]
\[
R_+=729u c_0\left(w^9-5w^6+w^7Tm\right).
\]

The exact identity

\[
t\,d\log v=(i^{-4}P_-+i^2R_+)\,dw
\]

has no hidden (L_0,T,w) denominator. The Cartan-reduced actual remainder is

\[
R_N=i^{-1}r_{-1}+i^{-2}r_{-2}+i^{-7}r_{-7},
\]
\[
\begin{split}
r_{-1}={}&(2\theta+2)(2\theta+3)(a_h-a_f)
  +2\theta(\theta+1)a_g\\
 &-(2-2\theta)(1-2\theta)(-2\theta)R_+,
\end{split}
\]
\[
r_{-2}=(1+2\theta)(3+\theta)a_f
 -(4\theta^2-2\theta)a_g/u,
\]
\[
r_{-7}=-(-4-2\theta)(-5-2\theta)(-6-2\theta)P_-.
\]

The proper denominators are at most (N_0^4,N_0^3,1), respectively. The
script `construct_n_only_hermite.py` performs exact complete Hermite
reduction in \(\mathbb Q(u)[w]\), requiring the final simple-pole numerator
to be zero and checking the full derivative identity for each component.
The completed run passed all three full derivative identities and all final
simple-remainder checks in 57.9 seconds. Its explicit primitive coefficients
are saved in `n-only-hermite-results.json`: the polynomial primitive degrees
are (12,2,24); the proper primitive denominator powers are (3,2,1) for
the first component and (2,1) for the second.

At a step (p/N_0^m), (m>1), take

\[
g=-(m-1)^{-1}p((N_0)_w)^{-1}\pmod{N_0},\quad\deg_w g<3.
\]

Subtracting \(d_w(g/N_0^{m-1})\) lowers the denominator by one. The final
simple-pole numerator is zero by the complete residue calculation above.
The polynomial part has its ordinary rational polynomial antiderivative.
This is a deterministic rational construction with no selected square
minor or denominator-degree trial.

## Restoring the literal scalar (K)

Let \(H_N'=R_N\), and define the rational Cartan correction

\[
C_{\rm tot}=E_{(D-6)(D-5)}(h)-E_{P_E}(F)-E_{P_D}(G)
 -E_{A^3}(vt)-W/v.
\]

Then the literal, fully differentiated scalar identity is

\[
S_{\rm src}-P_EF-P_DG-P_3H_{\rm pot}=(Z-1)K,
\qquad K=v(H_N+C_{\rm tot}).
\]

All terms in this formula are rational and explicitly specified by the
hashed arrays, finite differentiations, and cubic modular inverses.
For direct implementation the Cartan terms can also be written without
recursive operator notation. Put

\[
a=-v_i/v^2,\quad b=-v_J/v^2,\quad
\ell=6/v+2iv_i/v^2+2Jv_J/v^2,
\]

and, with ordinary (i,J) derivatives holding (w) fixed,

\[
\begin{split}
\mathcal E_S(X)={}&\ell(D-5)X
                 -(2i\partial_i+2J\partial_J)(\ell X),\\
\mathcal E_E(X)={}&\mathcal E_S(X)
  +a(Z+D/2-2)X+\partial_i[(1/v+\ell/2)X],\\
\mathcal E_D(X)={}&4J[bBX+\partial_J(bX)]+2bX\\
 &+a(Z+JB)X+\partial_i[(1/v+Jb)X],\\
\mathcal E_3(X)={}&aA^2X+\partial_i(aAX)+\partial_i^2(aX).
\end{split}
\]

Then

\[
C_{\rm tot}=\mathcal E_S(h)-\mathcal E_E(F)-\mathcal E_D(G)
             -\mathcal E_3(vt)-W/v.
\]

This includes every derivative of (v), including all (v_w) factors.
An equivalent source expression useful for evaluation is

\[
h=(v^2/v_w)i^{-1}\frac{54wT}{uN_0},
\]

which is exactly the physical (h), by the audited source-density identity.

## The retained original-kernel defect

With flat normalized base volume (dc\,dd\,de),

\[
Z=(c/3)\partial_c+(d/6)\partial_d+(e/6)\partial_e,
\quad\operatorname{div}Z=2/3,\quad B_0=-Z.
\]

For the original curve-valued section \(\chi\),

\[
e^{-7}(Z-1)K\,\chi
 =\operatorname{div}(e^{-7}K\chi Z)
   +e^{-7}K(B_0-1/2)\chi.
\]

The last term is still present. The construction of (K) is a positive
scalar rational reduction, **not** a primitive of the original source.
Serving this compact/normal-function defect remains necessary.
