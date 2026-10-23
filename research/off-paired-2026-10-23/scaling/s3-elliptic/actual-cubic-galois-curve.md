# A fixed j=0 elliptic Galois curve for the whole cubic

This is an exact source-carrying normalization. It is not a rational
primitive or a contraction of the physical source.

Start with the actual cubic-ray field and physical residue

\[
 H+Bp+Cp^3=0,\quad g=B+3Cp^2,\quad
 R=\frac{Bp}{g^3},\qquad R\,dx\wedge da\wedge du\wedge dv.
\]

Choose one root `rho³=H/C` and define

\[
 r=p/\rho,\qquad j=B/(C\rho^2).
\]

Then `r³+jr+1=0`. Its full S3 Galois closure is the fixed elliptic curve

\[
 E:\ Y^2=X^3-16,
 \qquad r=-4/X,\qquad j=(X^3-64)/(4X^2).
\]

The quotient by the order-three deck translations is the fixed elliptic
discriminant curve `E': V²=U³+432`, with the standard degree-three isogeny

\[
 U=4j=\frac{X^3-64}{X^2},\qquad
 V=-\frac{Y(X^3+128)}{X^3}.
\]

In particular, the actual nonconstant coupling `B` is retained as the
equation `4B/(C rho²)=U`; it is not declared independent or constant.

## Deck convention and physical descent

Take `P=(0,4i)` and define `T* f(Q)=f(Q+P)`. Then

\[
 T^*X=-8(4+iY)/X^2,
 \qquad
 T^*Y=-Y+(Y-4i)(X-T^*X)/X.
\]

This is an order-three translation, and `T*(U,V)=(U,V)`. The involution
`sigma(X,Y)=(X,-Y)` fixes `p=-4rho/X` and conjugates `T` to `T^-1`.
Thus the field fixed by `sigma` is the original normalized cubic field.
The three roots are `-4rho/X`, `-4rho/T*X`, `-4rho/(T*)²X`.

If `omega³=1`, the normalization-root deck transformation is

\[
 (\rho,X,Y)\longmapsto(\omega\rho,\omega X,Y).
\]

It leaves `p`, `H`, `B`, `C`, and the physical source fixed, and it
commutes with `T`. Hence this normalization does not introduce an
unaccounted physical character.

The exact source scalar becomes

\[
 R=\frac1{HC}\frac{jr}{(j+3r^2)^3}.
\]

It is `sigma`-even and has zero order-three trace:
`R+T*R+(T*)²R=0`. The same is true of the original four-form because the
deck action fixes the base coordinates and their volume. Therefore
`(1-T)^-1=(2+T)/3` and `(1+T)^-1=-T` on its standard character. These
operators can recover a primitive from a genuine primitive of a paired
source; they do not construct that paired primitive themselves.

## Exact relation to the fixed Fermat product

The whole-source Fermat normalization in
`../cm-product/whole-cubic-correspondence.md` remains in force. On its
finite cover the actual four-form is

\[
 -\frac{\alpha^{-4}\beta^{-4}}{144}R\,
 dH\wedge dC\wedge\frac{dU_1}{V_1}\wedge\frac{dU_2}{V_2}.
\]

The equation `U=4B/(C rho²)` pulls the fixed degree-three isogeny back to
this full Fermat product. An actual rational root along a proposed curve
`Gamma` requires a lift through that isogeny, with its discriminant square
root and root character retained. Merely mapping the density forms to
`E0×E0` or tracing them there does not supply such a lift.

Ambient CM graph classes alone do not give the needed standard character:
translation by `P` acts trivially on `H¹(E)`. A reducible incidence can
still supply individual components with nontrivial characters, so that
case requires its component and source calculation.

## A reducible physical incidence

The entire rank-three coupling satisfies

\[
 B+\frac1{3x}=
 \frac{(1+3x^2u/2)(1+x^2av)}{3x}.
\]

The two resulting supports in original homogeneous coordinates are

\[
 D_3=3X_1^2Y_1+2X_0^2Y_0,
 \qquad D_4=X_1^2X_2Y_2+X_0^3Y_0.
\]

On either, `B=-1/(3x)` exactly, with `H,C` still variable. Also

\[
 D_3D_4=6X_1F_{\rm mixed}+2X_0^5Y_0^2.
\]

These are explicit candidate incidence supports. Their total components
are deck invariant; a source-carrying component difference or a physical
normal current still has to be proved. The fixed first-power denominator
`D3 D4` was separately tested against the full certificate identity and
has no solution; that does not settle higher pole orders or geometric
currents on these supports.

The companion exact checker verifies the cubic, isogeny, translation,
three-root identities, source trace, and physical source normalization.

Prepared with OpenAI Codex assistance.
