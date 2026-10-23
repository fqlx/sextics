# Actual kernel reduced to a rational form on a quartic surface

This is a source-preserving reduction, not a primitive of the sextic.
It applies to the explicit rational K constructed from the actual Ssrc,
including all its dependence on the physical w cover and any permitted
source-preserving lift modifications.

Work with positive scalar forcing Ssrc. The final reconstruction for the
original target uses the opposite overall sign. Set

```
c=i e², d=j e, Jpar=j², ℓ=e q, h=e^-3,
Qquad=a²+b²+iℓ²+j aℓ+ℓ+1=0,
h=ab/ℓ³, h²=f(w)=1/v(i,j²,w).
```

The normalized canonical curve ab=q³ gives this pencil on the fixed
quadric exactly. The quadric is rational over the constant field: for
example its smooth projective closure has points at infinity after
adjoining sqrt(-1). Its physical base change h²=f(w) is retained throughout;
rationality of the quadric does not assert rationality or exactness of
that base change.

The base volume satisfies

```
dc∧dd∧de=e³ di∧dj∧de,
e^-7 K dc∧dd∧de=−(K/3) di∧dj∧dh.
```

For the relative curve form ζ=b dq/q, its wedge with the base volume
equals that for ζ0=b dℓ/ℓ. Let R=(Z−1)K, where Z=v∂v=−(h/2)∂h
at fixed i,j. Thus R=−h K_h/2−K, with K_h including the derivative
of the physical w cover. Relative to fixed i,j, the complete scalar
remainder is

```
ρ=−(R/3) ζ0∧dh.
```

There is an explicit first current on the retained cover:

```
ρ+d[(hK/6)ζ0]
 =K/6 [h dζ0+ζ0∧dh]
 =K h²/6 d(ζ0/h)
 =−K b²/(6ℓ⁴) da∧dℓ.
```

The last equality follows immediately from ζ0/h=ℓ² dℓ/a. It is a
literal two-form identity before using the quadric equation. Wedge it
with di∧dj to get the full four-form current; all other base derivatives
then vanish by repeated wedge factors. This avoids discarding a compact,
finite-section or infinity component in passing to the model.

The remaining two-form is even in b. Eliminate only b², retaining the
physical cover, to obtain the quartic surface

```
P=a⁴+jℓ a³+V a²+f(w)ℓ⁶=0,
V=iℓ²+ℓ+1, f(w)=1/v(i,j²,w).
```

Differentiating at fixed i,j,ℓ gives a_w=−f_w ℓ⁶/P_a. Therefore the
complete remaining source, in the orientation dℓ∧dw∧di∧dj, is

```
[K f_w ℓ²(a²+jℓa+V)/(6P_a)] dℓ∧dw∧di∧dj.
```

It is rational in the degree-four field Q(i,j,ℓ,w)[a]/(P). This gives a
finite algebraic integration problem. Its derivative matrix, rational
primitive, or a valid geometric serving argument still has to be
constructed; finite field degree alone does not imply integrability.

`verify_quadric_defect.py` passes thirteen exact symbolic identities:
the fixed quadric, full volume weight, all three free-coordinate two-form
components, the independent ζ0/h identity, and the complete quartic
source coefficient. The infinity-horizontal agent independently agrees
with the two-form and Jacobian signs. This does not constitute a
certificate, Lean verification, protected CI or acceptance.
