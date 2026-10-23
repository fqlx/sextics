# Source-bound removal of the artificial critical-fold poles

This is a constructive change of the actual source lift. It does not
integrate the remaining polynomial source and is not a sextic certificate.

Use the actual (K) from `N-ONLY-RATIONAL-LIFT.md`, with source SHA256
`d725307869fcf3a2f064a0a6616eee78ea59f74dd3305fcb1d2408d3018f25b5`.
This order-three fold construction applies to the **original CRT** cubic
potential, which is regular at the folds. One may normalize its integration
constant at (w=0). Properizing the **cubic** moment generally creates a
nonzero linear Morse jet and raises the resulting (K/v) fold order to five;
that modified input requires the more general fold construction and is not
covered by the order-three claim below. The direct quartic source Hermite
construction handles the order-five input with current denominator (C^3).

Write (H=K/v), and let (C(w)) be the monic saturated numerator of (v_w),
over (k=\mathbb Q(i,J)). Equivalently, with the notation of
`N-ONLY-RATIONAL-LIFT.md`, (C) is the monic associate of

\[
C_{\rm raw}=N_0TL_0+w(N_0)_wTL_0
             +2wN_0T_wL_0-wN_0T(L_0)_w.
\]

Its degree is 24. It is generically squarefree and coprime to (wTN_0L_0),
as proved by the exact specialized nonzero resultants in
`verify_actual_k_fixed_divisors.py`. All parameter denominators are retained.

## The actual lift-change operator

For every rational (Q), define

\[
\mathcal L_3Q=A^3Q+v(Z+JB+2)Z(Z+D/2+5)Q.
\]

The exact identity is

\[
P_3(vZQ)=(Z-1)(v\mathcal L_3Q).
\]

Thus replacing (H_{\rm pot}) by (H_{\rm pot}+vZQ) replaces

\[
H\longmapsto H-\mathcal L_3Q,
\]

while preserving the literal actual scalar source. Moreover

\[
\alpha(vZQ)=d_wQ,
\]

so this change preserves all residue equations, not merely the served
(N_0)-residues.

If (Q_w) is divisible by (C^2), then

\[
ZQ=\frac{wN_0TL_0}{C_{\rm raw}}Q_w
\]

is polynomial in (w), divisible by (wN_0TL_0C). It is therefore an
allowed boundary-compatible polynomial change of the CRT lift. Constants
between (C) and (C_{\rm raw}) belong to (k^\times).

## Only two negative Morse coefficients occur

At a critical section (w=r(i,J)), put

\[
V=v(i,J,r),\qquad s^2=v-V.
\]

The literal coordinate derivations are

\[
A=\partial_i|_s-\frac{V_i}{2s}\partial_s,
\quad B=\partial_J|_s-\frac{V_J}{2s}\partial_s,
\quad Z=\frac{V+s^2}{2s}\partial_s.
\]

They preserve parity. The initial moments have analytic one-form densities
at the folds; their scalar potentials therefore have only a possible
(s^{-1}) negative term. The quadratic source/potential operators yield
negative powers at most (s^{-5},s^{-3},s^{-1}); the cubic operator applied
to its regular potential has the same bound. Consequently

\[
H=A_3s^{-3}+A_1s^{-1}+O(1).
\]

Even negative terms are absent. This is a property of the actual source and
potentials, not an assumption on an arbitrary rational function.

Put (p=V_i,q=V_J),

\[
\mathsf H=V-Jq,\qquad \mathsf W=4V+ip+Jq,
\]
\[
\sigma=\frac{-p^3+V^2\mathsf H\mathsf W}{8}.
\]

For (Q=q_3s^3+q_5s^5+\text{even}+O(s^7)), the fully audited lower map is

\[
\mathcal L_3Q=-3\sigma q_3s^{-3}
 +\bigl(\mathcal Tq_3+15\sigma q_5\bigr)s^{-1}+O(1),
\]

where

\[
\begin{split}
\mathcal T=\frac38\bigl\{&
 (6p^2-2iV^2\mathsf H)\partial_i
 +2JV^2(\mathsf W-\mathsf H)\partial_J\\
 &+6pV_{ii}+2VJ(q\mathsf W+V\mathsf W_J)
   +3V^2\mathsf W+22V^2\mathsf H\bigr\},
\end{split}
\]

\[
\mathsf W_J=5q+iV_{iJ}+JV_{JJ}.
\]

This identity is independently checked in
`../verify_cubic_fold_lower_operator.py` and
`../../../audit/quadric-kernel/verify_fold_lower_map.py`.
The source-root symbol computation shows that \(\sigma\) is invertible in
(k[r]/C(r)): the specialized exact symbol gcd is one. Thus set

\[
q_3=-A_3/(3\sigma),\qquad
q_5=(A_1-\mathcal Tq_3)/(15\sigma).
\]

Both pole coefficients of the **actual** (H-\mathcal L_3Q) then vanish.
The lower coefficient retains every derivative of the actual (A_3) and
of the moving critical point.

## Rational data without adjoining a Morse square root

All following quantities belong to (k[r]/C(r)). Put

\[
a=v_{ww}(r)/2,\quad b=v_{www}(r)/6,\quad c=v_{wwww}(r)/24.
\]

Write the actual (H), in \(\lambda=w-r\), as

\[
H=k_3\lambda^{-3}+k_2\lambda^{-2}+k_1\lambda^{-1}+O(1).
\]

The odd-Morse condition gives

\[
k_2=-\frac{3b}{2a}k_3,
\]

and

\[
A_3=a^{3/2}k_3,\qquad
A_1=a^{1/2}\left[k_1-
 k_3\left(\frac{15b^2}{8a^2}-\frac{3c}{2a}\right)\right].
\]

Define

\[
t_3=-k_3/(3\sigma),\qquad
\mathcal T_a(t_3)=a^{-3/2}\mathcal T(a^{3/2}t_3),
\]

where the last expression is rational: replace every derivative
\(\partial_x\) in \(\mathcal T\) by
\(\partial_x+3a_x/(2a)\). Then put

\[
t_5=\frac{k_1-k_3(15b^2/(8a^2)-3c/(2a))-a\mathcal T_a(t_3)}{15\sigma}.
\]

The needed **rational** (w)-Taylor coefficients for (Q) are

\[
d_0=d_1=d_2=0,\quad d_3=a^3t_3,
\quad d_4=\frac32a^2bt_3,
\]
\[
d_5=a^3t_5+
 \left(\frac32a^2c+\frac38ab^2\right)t_3.
\]

These are the coefficients of (q_3s^3+q_5s^5) modulo \((w-r)^6\).
The formulas are invariant under (s\mapsto-s); no coefficient extension
or trace is used.

For actual coefficient extraction set (B=C^3H), which is regular at (C=0),
and (c_1=C_w(r),c_2=C_{ww}(r)/2,c_3=C_{www}(r)/6). Then

\[
k_3=B(r)/c_1^3,
\]
\[
k_1=\frac{B_{ww}(r)/2-3(c_2/c_1)B_w(r)
 +(6c_2^2/c_1^2-3c_3/c_1)B(r)}{c_1^3}.
\]

Critical-section derivatives are the rational induced derivations

\[
\partial_x^{\rm crit}=\partial_x-(C_x/C_w)\partial_w\pmod C,
\quad x=i,J.
\]

Thus all prescribed (d_j) are explicit finite rational operations on the
hashed actual (K), not unknown source potentials.

## A consistent global interpolation, including fixed boundaries

Choose for example the fixed boundary factor

\[
W_0=w^2T^2N_0^2L_0^2.
\]

It is coprime to (C). Start (Q=0). For (j=3,4,5), in that order, take

\[
E_j=\frac{d_j-Q^{(j)}/j!}{W_0(C_w)^j}\pmod C,
\qquad \deg_w E_j<24,
\]

and update

\[
Q\longleftarrow Q+W_0C^jE_j.
\]

The denominator is invertible modulo (C). This update preserves all lower
Taylor coefficients at every critical point and fixes the (j)-th one.
After the three updates, (Q) is divisible by (W_0C^3), so (Q_w) is
divisible by (C^2) and (ZQ) is a boundary-compatible polynomial CRT
change. The prescribed six jets match at **all** folds. This triangular
construction proves consistency; it is not an assumed invertible selected
minor of an overdetermined system.

The resulting actual source-preserving potential is

\[
H_{\rm pot,new}=H_{\rm pot}+vZQ,
\quad K_{\rm new}=K-v\mathcal L_3Q.
\]

Its (K_{\rm new}/v) has no fold poles. The fixed-boundary audit proves it
has no other finite poles, hence it is polynomial in (w) over (k).
The chosen (W_0) preserves the existing (w=0) regularization.

The actual interpolation coefficients have not been expanded into a large
array. The equations above give their deterministic rational construction
from the actual source. Infinity polynomial growth may increase under this
interpolation and remains part of the problem. Polynomial in (w) does not
mean polynomial in (f=1/v); the latter stronger property would allow the
quartic rational integration supplied by the quartic-kernel construction.
