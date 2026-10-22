# Residual correction interface

These sources formalize assembly and a return to the full certificate
contract. Applications supply their exact source, operator and coordinate
transport. The modules compile with the pinned toolchain and
pass kernel replay. Their new declarations use only the permitted axioms
`propext`, `Classical.choice`, and `Quot.sound`. The identities below describe
the mathematical interface and its remaining application obligations.

## Fixed source and operator

Fix additive groups `X`, `Y`, an additive operator `L : X →+ Y`, and a source
`S : Y`. A contribution supplies an element `delta k` and an exact identity

\[
 L(\delta_k)=R_k-R_{k+1},\qquad R_0=S.
\]

`ResidualCorrections.lean` records this as `Correction`, composes adjacent
steps, and telescopes finite chains. Additivity gives

\[
 L\left(\sum_{k=0}^{n-1}\delta_k\right)
 =\sum_{k=0}^{n-1}(R_k-R_{k+1})=S-R_n.
\]

The same conclusion holds if each step supplies only a proof of existence.
This is a finite statement; an infinite series would additionally require
convergence and compatibility of the operator with its limit. Completion
requires a proof of `R n = 0` and a return theorem to the original target.
Two identities each removing `S` cannot be composed as adjacent corrections
unless their stated remainders actually match.

## Translation into common coordinates

For operators `L`, `L'`, supply additive maps `T` on corrections and `U` on
sources, together with the exact commuting identity

\[
 L'(T x)=U(Lx).
\]

Then the translated correction removes `U before - U after`. The source map
need not be injective, so the interface accommodates normalized field trace.
A commuting identity is an application obligation, not a consequence of
naming a coordinate change.

For a normal chart at pole order one, the existing shared construction gives
a concrete choice. Let `rho` evaluate into the residue function field, put
`g = rho (∂₀ F) ≠ 0`, and let `E i` be the induced tangent derivations. Then

\[
 S=\frac{\rho(\partial_0 A)g-\rho(A)\rho(\partial_0^2F)}{g^2},
 \qquad
 L(w)=-\sum_i\left(E_i(w_i)-w_i\frac{E_i(g)}g\right).
\]

Intermediate remainders lie in this field; they need not be normal sources of
polynomial numerators. A proof `L w = S` yields the weighted equation used by
`HoldoutConstruction.finite_residue_solution_clearing_value` in
[`FiniteResidueClearing.lean`](Constructions/HoldoutCover/FiniteResidueClearing.lean).
Its explicit hypotheses include the quotient kernel, the normal chart,
irreducibility, compatible derivations and the entire source trace. It
produces a legal polynomial denominator, normalized E1, and E2 with a general
quotient. The homogeneous sextic/source and prime hypotheses and a valid
normal chart then allow `HoldoutConstruction.hasCertificate_of_normalized`
in [`HomogeneousCertificate.lean`](Constructions/HoldoutCover/HomogeneousCertificate.lean)
to prove the original `HasCertificate F A 1` statement.

Density and Jacobian factors must be included in these maps. In the notation
of `CycleResidueTransport.piola_pullback` in
[`Density.lean`](Constructions/ResidueTransport/Density.lean), the pullback is

\[
 T(w)=\frac gh\det(M)M^{-1}w,
 \qquad U(r)=\frac gh\det(M)r.
\]

The theorem requires the inverse matrices, chain rule and mixed-derivative
identities. On a finite cover, trace the entire transformed source and every
field component, including these multipliers. Moving maps also require their
parameter derivatives: `CycleMovingMap.residue_source_from_jet` in
[`MovingMap.lean`](Constructions/ResidueTransport/MovingMap.lean) retains an
explicit scalar differential correction. Its conversion to the chosen
weighted vector operator still needs proof. A frozen slice does not supply
these identities.

## Full rational certificate operator

[`RationalCertificate.lean`](RationalCertificate.lean) gives a second concrete
interface for every pole order. Fix an injective polynomial evaluation `phi`
into a field and actual coordinate derivations `Delta`, with
`Delta i (phi p) = phi (∂ᵢ p)`. Write `f = phi F` and define

\[
 \mathcal L_{f,q}(v,c)
 =q\sum_i\Delta_i(f)v_i-f\sum_i\Delta_i(v_i)+f^{q+1}c.
\]

Including `c` in the correction keeps this operator additive while retaining
the unrestricted quotient. For a polynomial representative set

\[
 v_i=\frac{\phi(N_i)}{\phi(D)},\qquad
 c=\frac{\phi(Q)}{\phi(D)^2}.
\]

The quotient rule gives

\[
 \sum_i\Delta_i(v_i)
 =\frac{\phi(D\operatorname{div}N-N(D))}{\phi(D)^2}.
\]

Multiplying `mathcal L(v,c) = phi A` by `phi(D)²` and using injectivity is
equivalent to the original identity

\[
 AD^2-qD N(F)+F\bigl(D\operatorname{div}N-N(D)\bigr)
 =F^{q+1}Q.
\]

`verify_iff_rationalCertificateOperator` additionally requires exactly the
denominator nonvanishing, homogeneous degrees and coprimality fields of
`Verify`. `hasCertificate_of_rational_corrections` telescopes rational
corrections and applies this return theorem once to the total. Individual
remainders need not themselves represent polynomial sources. The total's
legal homogeneous representatives remain an obligation; no bound on their
denominator degree or requirement `Q = 0` has been introduced. An injective
evaluation alone does not enforce admissibility: if `f ≠ 0`, the unrestricted
pair `(0, phi A / f^(q+1))` already maps to `phi A`, but its poles along `F`
prevent the required legal representation in general. Thus a zero remainder
for unrestricted rational pairs is insufficient without the return
obligations. An injective evaluation of the complex polynomial ring cannot be
replaced by a finite-characteristic sample or a restriction to a slice. Residue-field
evaluation is also not injective on the ambient ring and uses the separate
residue-clearing return path above.

If each removed source already has a polynomial certificate,
`HasCertificate.telescope` and `HasCertificate.of_remainder_zero` in
[`CertificateOperations.lean`](CertificateOperations.lean) give a sufficient
special case. They use `Verify.add` to preserve different legal denominators
and both quotient terms. They are not a requirement on residue-field steps.

## Obligation for a research contribution

Each contribution must identify the fixed source and operator, its incoming
and outgoing remainders, its correction or existence proof, and the exact
translation identity. It must account for densities, moving-coordinate
derivatives and full cover traces whenever those occur. The final assembly
also needs a zero remainder and the chosen return theorem's legality,
homogeneity and coordinate hypotheses. Exact characteristic-zero proofs
discharge these obligations; slices and finite-field samples provide
preliminary evidence.
