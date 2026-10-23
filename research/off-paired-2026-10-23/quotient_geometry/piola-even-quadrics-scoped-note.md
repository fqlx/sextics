# Scoped structural note on six globally Y-even quadratic outputs

Status: research argument awaiting independent review. This is not a
classification of finite polynomial Piola maps, a certificate, or a claim
about parity-mixed outputs and other weight profiles. No bounded search was
performed.

Suppose the immutable smooth sextic has an exact composition `F=G(q)` with
six globally Y-even quadratic forms, and `G` is an ordinary homogeneous
cubic. Each output has the form `q_i=q_iX(X)+q_iY(Y)`. The finite-map
theorem of docs/03-geometric-support.md, section 3.4, would make `G=0`
smooth in P5 and both restrictions `qX,qY` basepoint free: a nonzero common
zero of either restriction would give a singular point of the corresponding
Fermat sextic.

Let `r` be the rank of the six X-quadratic forms. The absent bidegree
`(2,4)` component says

```
sum_i q_iX(X) * G_i(qY(Y)) = 0.
```

Consequently the gradient image of `qY(P2)` is contained in the projective
annihilator of the span of `qX`, of dimension `5-r`. Both `qY` and the
gradient map of the smooth cubic are finite onto their images: their
pullbacks of O(1) are O(2), which are ample. The image has dimension two,
so `r<=3`. Basepoint freeness of `qX` gives `r>=3`. Thus `r=3` and its
three-dimensional net defines a finite quadratic map `Q:P2_X -> P2` of
degree four.

The bidegree `(4,2)` component then forces its three actual quartic
coefficients

```
W1=X0^3*X1, W2=X1^3*X2, W3=X0^2*X1*X2
```

to be quadratic polynomials in the coordinates of Q. Therefore
`K0=C(W1/W3,W2/W3)` is a subfield of `K=C(Q1/Q3,Q2/Q3)`.
But

```
W1/W3 = X0/X2,
W2/W3 = X1^2/X0^2,
[C(P2):K0] = 2,
[C(P2):K] = 4.
```

The field tower is incompatible with `K0` being a subfield of `K`.
Nonzero numerical coefficients in the original three mixed monomials do
not change this argument.

An independent geometric way to see the last incompatibility was supplied
by the surface-incidence child: the common divisor of W is precisely the
line `X1=0`. Its image under a finite quadratic map is a line or conic.
Three independent target conics containing that image are impossible if
the image is a conic; if it is a line, their pullbacks have a common
quadratic divisor, contrary to the degree-one common divisor of W.

The positive polynomial-map problem therefore remains focused on
parity-mixed quadrics or other weight profiles. No actual composition or
Jacobian-density binding has been found in this work.
