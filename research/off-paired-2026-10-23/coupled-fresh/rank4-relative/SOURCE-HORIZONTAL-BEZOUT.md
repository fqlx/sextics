# Exact source-guided genuine horizontal currents

This constructs rational U,W which exactly cancel the forcing's transverse
flux term in the complete bare-coordinate PDE. It is not a full current:
the remaining ordinary horizontal divergence must still be matched by the
fourth-order adjoint or by the free Hamiltonian correction below.

Keep H,q,N from `BARE-FULL-HORIZONTAL-CLOSURE.md`, and put

    L=z/a+2q/(9a^2),
    K=3az+12z^5,
    M=−18a^3+54az^6,
    Q=q^2+Kq+M.

The actual physical derivatives satisfy

    H_a−L H_z=−Q/(9a^2).

Reducing H_z modulo Q gives the linear remainder E q+F:

    J5=−9/a [q^3−Kq^2+(K^2−M)q−K^3+2KM],
    E=1/2−9(K^4−3K^2M+M^2)/a,
    F=6z^5−3az/4−9(K^3M−2KM^2)/a,
    H_z=J5 Q+E q+F.

Let

    R0=F^2−KEF+ME^2,
    w1=[−F(K^2−M)+KME]/(6a^2 R0),
    w0=M(EM−KF)/(6a^2 R0),
    Wb=w1 q+w0,
    V=(K−q)/(6a^2)−Ew1−J5 Wb.

The resultant R0 is nonzero: at a=1,z=0 it is
`−18*(5831/2)^2`. Thus the following are actual rational functions:

    U0=−9a^2 V,
    W0=Wb+9a^2 L V.

They satisfy the exact source constraint

    H_a U0+H_z W0=−q^3/(6a^2).

These are polynomial in C of degrees at most four and five respectively,
with rational functions of a,z as coefficients. Their construction is a
Euclidean identity for the physical H derivatives, not a degree-family
search. In particular no inverse P_a or C-dependent denominator is used.

Inserting them in the complete bare scalar equation cancels its whole
explicit transverse forcing, leaving

    Lhat_delta* G = partial_a U0+partial_z W0.

A particular G solving this remaining equation has not been found. The
normal-constraint freedom is explicit: for arbitrary rational S,

    U=U0+S H_z, W=W0−S H_a

preserves the exact source constraint, and changes the remaining divergence
by

    H_z partial_a S−H_a partial_z S.

Thus a sufficient genuine-horizontal construction is the actual coupled
rational equation

    Lhat_delta* G
      =partial_a U0+partial_z W0
         +H_z partial_a S−H_a partial_z S.

Neither G nor S is set to zero by the construction. Once solved, the full
four-component reconstruction in `BARE-FULL-HORIZONTAL-CLOSURE.md` applies.

`verify_source_bezout.py` checks the generic Euclidean source identity,
its exact binding to the displayed physical H, and nonvanishing of R0.
No complete certificate is asserted.
