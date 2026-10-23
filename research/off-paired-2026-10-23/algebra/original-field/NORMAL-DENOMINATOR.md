# Auxiliary normal and complex coprimality

This is a mathematical side-condition argument, not a sextic certificate or a Lean proof. The six elementary bindings in `verify_normal_denominator.py` pass over exact rational arithmetic. The factor argument below is separate from those computations.

Let `G` have weights `(0,1,1,-1,0,-1)` in the fixed original variable order. Then `G(F)=3J`, where

```
J=2(X1^6+X2^6-Y0^6-Y2^6)+X1^3 X2 Y1 Y2/2.
```

Every nonzero G-homogeneous polynomial is relatively prime to F over the complex numbers. Indeed, the connected multiplicative torus acts on the finite set of irreducible factors of a torus eigenvector, so each factor is itself a torus eigenvector. If such a factor divided F, it would divide each weight component of F. In particular it would divide both `X1^6+X2^6` and `Y0^6+Y2^6`, which are coprime because they have disjoint variable sets. This is impossible. No irreducibility assumption on F is needed.

Also `gcd_C(F,J)=1`. The polynomial F is squarefree: it is monic of degree six in Y1, and its resultant with its Y1 derivative is nonzero, as seen by specializing X0=1 and all remaining variables other than Y1 to zero. The specialization is `Y1^6+1`, with nonzero resultant 46656. If an irreducible H divided both F and G(F), squarefreeness would imply `H | G(H)`. Since G preserves ordinary degree, `G(H)=lambda H` for a complex constant lambda. Thus H would be G-homogeneous, contradicting the preceding paragraph.

For completeness, smoothness also follows by elementary gradient dominance: at a nonzero coordinate of maximum modulus, the pure derivative has modulus `6|z|^5`, while the sum of absolute mixed coefficients in each derivative is at most one of `13/6,7/3,5/6,5/6,1,5/6`, all strictly less than six. This supplies no primitive for the target.

These facts can justify denominators of the form `J^m E` with nonzero G-homogeneous E after an actual original-coordinate identity is found. They do not establish that identity.
