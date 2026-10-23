# Saturated projective incidence model

`../build_projective_model.py` constructs exact homogeneous equations for
the proposed compactification in

`P1_(q0:q1) x P1_(h0:h1) x P1_(v0:v1) x WP(1_U,2_t,1_z)`.

`model.pickle` contains the rational equations and their Cox-ring
homogenizations. Every monomial's four degrees and exact replay in the
affine chart q0=h0=v0=z=1 are checked by the builder. The three degrees are

```
(12,8,4,6), (6,7,3,6), (12,6,4,6).
```

The main compactification is the closure of the intended open component:

```
J = (E1,E2,E3),
f = q0*h0*v0*h1*(h1²-4h0²)*v1*U*z
    *(v1²-v0²)*(v1²-ell*v0²),
I = J : f^infinity.
```

This is an explicit ideal-theoretic model; a full finite generating set
for its saturation has not yet been computed. Generic geometric
irreducibility comes from the independently studied 27-sheet slope cover
and its intrinsic quadratic cover, not merely from the definition above.
The saturation retains the union of all components meeting the open set;
any final irreducibility claim must retain that separate input.

The exact modular replay at q=2,h=5,ell=46 in F109 produces a reduced
54-point fiber (Jacobian singular locus empty). Its script and receipt are
`fiber_mod109.sing` and `fiber_mod109.log`.

**The raw global J is not a complete intersection.** All three equations
vanish on q0=v0=0, and also on h0=v0=0. These codimension-two boundary
components are not Cox-irrelevant. Thus the formal sum-of-degrees shift
(28,19,9,14) is not the canonical sheaf of the desired main component, and
CI linkage using the raw J is invalid globally. The safe canonical-module
target after saturation is

```
Ext^3_R(R/I,R)(-2,-2,-2,-4)
```

followed by Cox sheafification. A locally verified complete-intersection
presentation on an open chart can still use linkage there, but does not
determine how that module extends at the projective boundary.

`global_mod109.sing` attempts the saturation with the actual nine-variable
Cox equations. Two 50-second bounded runs reached only the start marker;
they produced no saturation or canonical-module generators. The q=2
four-variable affine curve attempt is separate and must not be mistaken
for a global surface calculation.

Even the canonical module of the saturated singular compactification is
only one stage of the global irregularity calculation: the resolution
adjoint module pi_*omega_S is needed for H1(S,omega_S), with its U-odd
part selected. None of these scripts asserts a global odd one-form or a
serving certificate.
