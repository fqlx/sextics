This packet binds the actual cyclic-triple-residual source to the characters
and generic adjoint jets at the new D32 conductor/Fermat corner. Run:

```
python source_transition.py
```

The script reads the pinned `instance.rec` and original 558-term D32 graph,
checks the literal sextic and target, and computes the coordinate Jacobian.
On `Y2=1`, put `X0=eps, X1=v*eps, X2=W, Y1=b` and
`a=Y0`, with `a^6+1=b*r`. In the ordered volume
`deps,dW,db,dr,dv`, the actual source is

```
 -eps^4*b/(6*a^2) * volume/F^2.
```

The standard projective Omega convention fixes this sign. For a homogeneous
degree32 canonical polynomial `g`, division of the graph by `eps^17*b^2`
gives local canonical coefficient `g/(6*a^5*eps^16*b)`. The conductor factor
`b` is essential. Its generic weighted model and divisibility are independently
checked in `../fresh/boundary/weighted_ci_audit.py`.

On the overlap `eps'=v*eps, v'=1/v`, with `W,b,r` unchanged, the relative CI
canonical frame scales by `v^18`; the total frame including `dv` scales by
`-v^16`. The six low adjoint jets are `1,eps,eps^2,b,r,W^3`. The source's
mu3 character is the character of the CI canonical frame. Global Y sign
sends both `eps` and `W` to their negatives and leaves that frame invariant,
so the relevant even jets are `1,eps^2,b,r`.

The script verifies explicit degree32 polynomial families realizing each
generic jet, including the first radial order16 and the conductor condition.
Across the six `a^6=-1` corners, the canonical unit is
`1/(6*a^5)=-a/6`. Thus the six monomials `Y0^j*Y2^(d-j)`, `0<=j<=5`, give
an invertible coefficient matrix. Tensoring with the permitted powers of
`v` gives rank420 for the four even generic jet families. The source's finer
diagonal character reduces this to rank140, with its explicit congruences
recorded in JSON.

This is a generic-overlap and source-character calculation. The actual
weighted family degenerates at special v, including infinity. The coherent
extension across those points, all other global adjoint conditions, and the
actual Gysin preimage of the source are separate questions. In particular,
rank420/140 does not assert global adjoint surjectivity or exclude this support.

Fresh owns the infinity model. In that chart `u=1/v`, `eps'=X1`, the literal
source is `+u^3*eps'^4*b/(6*a^2)` times the corresponding ordered volume/F²;
its extra `u^3` zero may matter in a source-specific restriction calculation.

The finite special point `v^6+1=0` is now treated in
`special_P_series.py`, `special_P_audit.py`, and `special_P_proof.md`.
Replay them in that order. The literal graph gives a rational universal
weighted model with weights `(1,1,4,2,4)` and degrees `(6,8)`. Its first
exceptional surface has nine Du Val points and one inherited generic corner.
The latter's next weighted initial model is quasismooth over QQ. The old
generic adjoint ideal automatically meets the new valuation; extending
through the remaining rational charts introduces no further adjoint
condition. The exact computational statements and the standard geometric
extension facts used in that final implication are separated in the proof.
This finite-P0 conclusion does not settle the new infinity valuations or
other boundary components.
