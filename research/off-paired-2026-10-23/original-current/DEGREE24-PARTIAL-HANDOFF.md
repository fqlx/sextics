# Frozen original-coordinate partial current

**UNSOLVED. This is an exact partial identity for the immutable original target, not a certificate.** Research was stopped at the user's request. No Lean proof, local kernel check, protected CI, acceptance, or publication was performed for this partial current.

The reproducible computation is `build_degree24_partial.py`; its complete expanded target, denominator, six numerators and nonzero remainder are in `degree24-partial-current.json` (SHA256 `a53a1aa92aacedfdedf42ef9d17df088efdb1ca1480893ea9ea28a2894eca03b`). Run it with `/workspace/tooling/sextics-venv/bin/python`. It completed successfully using native exact rational multivariate FLINT arithmetic, without numerical sampling.

## Checked identity and remaining task

In variable order `(X0,X1,X2,Y0,Y1,Y2)`, with exactly the requested `F`, `A=X0^3 Y0^3` and `q=1`, the computation proves

```
A D^2 - D sum_i(N_i F_i) + F(D div N - N.grad D) = F R48.
```

`D` is nonzero homogeneous degree 24, all nonzero `N_i` have degree 25, and `R48` is a nonzero homogeneous degree-48 polynomial with 24 terms. Exact division also verifies **F does not divide R48**. Thus the required right side `F^2 Q` has not been obtained. The vector field removes the leading normal-pole term and leaves the explicitly retained next term. No pending computation is needed to establish this partial identity or its failure to be a certificate.

## Small factored presentation

Write `A=X0^3 Y0^3`, `m=X1^3 X2 Y1 Y2` and

```
K = 3 X2^6 Y2^6 Y1^6 - 3 X2^6 Y2^6 X0^6
    - 8 X2^6 Y0^6 Y1^6 + X2^6 Y0^6 X0^6
    - X1^6 Y2^6 Y1^6 + 2 X1^6 Y2^6 X0^6
LR = 3(X1^6+X2^6)[(Y2^6-Y0^6)X0^6+Y1^6(3Y0^6-Y2^6)]
LK = 2(X1^6 Y2^6-X2^6 Y0^6)(X0^6-2Y1^6)
LZ = (X0^6+Y1^6)(X1^6 Y2^6-X2^6 Y0^6).

D  = 3mK
N0 = 0
N1 = 2A X1(K-LK)
N2 = 2A X2(K+LR-LK)
N3 = 2A Y0(3LZ-2LK-K)
N4 = 6A Y1 LZ
N5 = 2A Y2(LK+3LZ-LR-K).
```

An exact compact description of the remainder uses `R=X2^6/X1^6`, `S=Y2^6/Y0^6`, `W=Y1^6/X0^6`:

```
delta = 3RSW-3RS-8RW+R-SW+2S
nr = 3(1+R)[S-1+W(3-S)]
nk = 2(S-R)(1-2W)
nz = (1+W)(S-R)
p = 2(nz+nk-delta)delta
    - 2R nr delta_R - S(6nk-2nr)delta_S - 6W nz delta_W
P36 = (X1^6 Y0^6 X0^6)^2 p(R,S,W)
R48 = 18 A m P36.
```

`P36` is polynomial. At `R=S=W=1`, `delta=-6`, `p=120`; the rational residual coefficient `p/delta^2` is `10/3`. The JSON retains all expanded terms so that neither this check nor the construction relies on a coordinate-chart assertion.

## Source/current origin and sign boundary

This field comes from the actual source-carrying raw j-current, rather than a universal-density trace. On `X0=1`, let `(x,u,y,z,p)=(X1,X2,Y0,Y1,Y2)`, `a=x^3`, `b=y^3`, `q=xy`, `r=u^3/x^3`, `k=up/(xy)` and

```
J=2(x^6+u^6-y^6-p^6)+x^3 u z p/2
Nnormal=(x d_x+u d_u-y d_y-p d_p)/(3J)
Nnormal(F)=1
muF=q/(9rJ) dq wedge dr wedge dk wedge dz.
```

The actual canonical source has sign `+div(b Nnormal) muF`. Accordingly an exact source primitive represented by the tangent field `w` contributes the ambient field `b Nnormal-w`. The raw descended current is `U1=-v ydesc^2 dxdesc/(xdesc^3 Jbar)` and obeys the literal source identity `partial_j U1=(4-Dnorm)nu_b`; its weighted current retains the correction `-t_j U1`, with `j` differentiated at fixed `(i,v)`. The pullback keeps the density; the weighted-current correction remains in the explicit residual rather than being discarded. The resulting quadratic deck parity is even, so the displayed field is rational in original coordinates without a trace operation.

The simple field above is obtained after dropping an explicitly F-multiple normal-field correction. Such a change affects the certificate expression only by an F-squared term. The final exact six-variable FLINT identity is the definitive checked statement; the geometric description does not turn its nonzero remainder into a solution. Full generic compact fiber-connection arrays are not needed to rerun this partial identity.

## Denominator side condition: mathematical argument only

For the torus derivation `Graw` with variable weights `(0,1,1,-1,0,-1)`, the computation checks `Graw(D)=3D`. Every irreducible factor of a nonzero torus weight-homogeneous polynomial is weight-homogeneous: the connected torus cannot permute a finite set of irreducible factors nontrivially. A weight-homogeneous factor of F must divide each of its weight components. In particular it would divide both `F_6=X1^6+X2^6` and `F_-6=Y0^6+Y2^6`, which are relatively prime over C because they use disjoint variables. Thus `gcd_C(F,D)=1`.

This is a mathematical coprimality argument, **not a Lean/kernel-verified proof**. It does not require an unproved irreducibility or squarefreeness assertion about F. The denominator does satisfy the claimed side condition by this argument, but the nonzero remainder still prevents a certificate.

## Related independently checked interfaces

See `../audit/theta/COMPACT-SOURCE-AUDIT.md` for the generic compact-connection, full-base connection, source-density/Euler and actual j-current audits. In particular `verify_j_source_current.py` recorded 45 exact generic checks and `verify_full_base_connection.py` recorded 886. These checks establish current interfaces; none establish full source closure. The previous mathematical and verification status remains **UNSOLVED**.
