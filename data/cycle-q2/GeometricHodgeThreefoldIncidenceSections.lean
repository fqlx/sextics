import Proposal.GeometricHodgeThreefoldIncidence
import Proposal.GeometricHodgeTwistRatios

/-!
# Incidence specialization preserves the normalized homogeneous sections

Transport through the equality of the two homogeneous ideals preserves
each section p/Xᵢⁿ on every subopen of the i-th affine chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 90000
set_option maxRecDepth 2500
noncomputable section
namespace CycleQ2GeometricHodgeThreefoldIncidence

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceFamilyContainment
open CycleQ2GeometricProjectiveCurve.HomogeneousQuotient
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {R : Type} [CommRing R]

private abbrev HIdeal (R : Type) [CommRing R] :=
  { I : Ideal (MvPolynomial (Fin 5) R) // I.IsHomogeneous (PolynomialGrade R) }

private abbrev grades (I : HIdeal R) := CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
  (PolynomialGrade R) I.val

private instance modelGradedRing (I : HIdeal R) : GradedRing (grades I) := gradedRing _ _ I.property

private abbrev space (I : HIdeal R) : Scheme := Proj (grades I)

private abbrev openAt (I : HIdeal R) (i : Fin 4) : (space I).Opens :=
  Proj.basicOpen (grades I) (Ideal.Quotient.mk I.val (X i.castSucc))

private def sectionAt (I : HIdeal R) (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : Γ(space I, openAt I i) :=
  Proj.awayToSection (grades I) (Ideal.Quotient.mk I.val (X i.castSucc))
    (Away.mk (grades I) (show Ideal.Quotient.mk I.val (X i.castSucc) ∈ grades I 1 from
      ⟨X i.castSucc, by
        change (X i.castSucc : MvPolynomial (Fin 5) R).IsWeightedHomogeneous geometricWeight 1
        simpa only [CycleQ2SeedFermatProj.geometricWeight_castSucc] using
        (isWeightedHomogeneous_X R geometricWeight i.castSucc), rfl⟩) n
      (Ideal.Quotient.mk I.val p) (by
        refine ⟨p, ?_, rfl⟩
        simpa using hp))

attribute [-instance] modelGradedRing

variable [Algebra ℂ R] (y : ParameterIndex → R)

def nativeNormalized (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : Γ(weightedThreefold y, nativeOpen y i) :=
  sectionAt ⟨sexticIdeal y, sexticIdeal_homogeneous y⟩ i n p hp

def nativeRestriction (i : Fin 4) (V : (threefold (sexticEval y)).Opens)
    (hi : V ≤ coordinateOpen (sexticEval y) i) :
    Γ(weightedThreefold y, nativeOpen y i) →+* Γ(threefold (sexticEval y), V) :=
  ((nativeIso y).hom.appLE (nativeOpen y i) V
    (hi.trans (nativeIso_preimage y i).ge)).hom

def movingSection (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n)
    (V : (threefold (sexticEval y)).Opens) (hi : V ≤ coordinateOpen (sexticEval y) i) :
    Γ(threefold (sexticEval y), V) :=
  CycleQ2HodgeTwistRatios.normalized (sexticEval y) i (n := n) (quotient (sexticEval y) p)
    (quotient_mem_grade (sexticEval y) (n := n) p hp) V hi

private def movingIdeal : HIdeal R :=
  ⟨Ideal.span {equation (sexticEval y)}, Ideal.homogeneous_span _ _ (by
    rintro q (rfl : q = equation (sexticEval y))
    exact ⟨6, equation_homogeneous _⟩)⟩

private def pointIdeal : HIdeal R := ⟨sexticIdeal y, sexticIdeal_homogeneous y⟩

private theorem ideal_eq : movingIdeal y = pointIdeal y := Subtype.ext
  (congrArg (fun q : MvPolynomial (Fin 5) R => Ideal.span {q}) (equation_eq y))

private structure SectionData where
  carrier : Scheme.{0}
  chart : carrier.Opens
  value : Γ(carrier,chart)

private def restrictFrom (A B : SectionData) (e : A.carrier ≅ B.carrier)
    (h : e.hom ⁻¹ᵁ B.chart = A.chart) (V : A.carrier.Opens) (hv : V ≤ A.chart) :
    Γ(A.carrier,V) :=
  e.hom.appLE B.chart V (hv.trans h.ge) B.value

private def restrictAt (A : SectionData) (V : A.carrier.Opens) (hv : V ≤ A.chart) :
    Γ(A.carrier,V) := A.carrier.presheaf.map (homOfLE hv).op A.value

private theorem transport_preimage {A B : SectionData} (he : A = B)
    (e : A.carrier ≅ B.carrier) (hIso : e = eqToIso (congrArg SectionData.carrier he)) :
    e.hom ⁻¹ᵁ B.chart = A.chart := by
  subst B
  subst e
  simp

private theorem restrictFrom_eq {A B : SectionData} (he : A = B)
    (e : A.carrier ≅ B.carrier) (hIso : e = eqToIso (congrArg SectionData.carrier he))
    (V : A.carrier.Opens) (hv : V ≤ A.chart) :
    restrictFrom A B e (transport_preimage he e hIso) V hv = restrictAt A V hv := by
  subst B
  subst e
  simp [restrictFrom,restrictAt,Scheme.Hom.appLE]

private def fromIdealSection (I : HIdeal R) (i : Fin 4) (n : ℕ)
    (p : MvPolynomial (Fin 5) R) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    SectionData := ⟨space I, openAt I i, sectionAt I i n p hp⟩

private def familyChartSection (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : Γ(threefold (sexticEval y),
      coordinateOpen (sexticEval y) i) :=
  Proj.awayToSection (grade (sexticEval y)) (coord (sexticEval y) i.castSucc)
    (Away.mk (grade (sexticEval y)) (weightOne_mem_grade (sexticEval y) i) n
      (quotient (sexticEval y) p) (by simpa using quotient_mem_grade (sexticEval y) p hp))

private def familyData (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : SectionData :=
  ⟨threefold (sexticEval y), coordinateOpen (sexticEval y) i, familyChartSection y i n p hp⟩

private def pointData (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : SectionData :=
  ⟨weightedThreefold y, nativeOpen y i, nativeNormalized y i n p hp⟩

private theorem data_eq (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : familyData y i n p hp = pointData y i n p hp := by
  change fromIdealSection (movingIdeal y) i n p hp = fromIdealSection (pointIdeal y) i n p hp
  exact congrArg (fun I => fromIdealSection I i n p hp) (ideal_eq y)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 900000 in
theorem nativeIso_normalized (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n)
    (V : (threefold (sexticEval y)).Opens) (hi : V ≤ coordinateOpen (sexticEval y) i) :
    nativeRestriction y i V hi (nativeNormalized y i n p hp) = movingSection y i n p hp V hi := by
  exact @restrictFrom_eq (familyData y i n p hp) (pointData y i n p hp)
    (data_eq y i n p hp) (nativeIso y) rfl V hi

private theorem transport_inv_preimage {A B : SectionData} (he : A = B)
    (e : A.carrier ≅ B.carrier) (hIso : e = eqToIso (congrArg SectionData.carrier he)) :
    e.inv ⁻¹ᵁ A.chart = B.chart := by
  subst B
  subst e
  simp

set_option maxRecDepth 5000 in
set_option maxHeartbeats 650000 in
theorem nativeIso_inv_preimage (i : Fin 4) :
    (nativeIso y).inv ⁻¹ᵁ coordinateOpen (sexticEval y) i = nativeOpen y i := by
  let h := isWeightedHomogeneous_zero R geometricWeight 0
  exact @transport_inv_preimage (familyData y i 0 0 h) (pointData y i 0 0 h)
    (data_eq y i 0 0 h) (nativeIso y) rfl

end CycleQ2GeometricHodgeThreefoldIncidence
end

#print axioms CycleQ2GeometricHodgeThreefoldIncidence.nativeIso_normalized

#print axioms CycleQ2GeometricHodgeThreefoldIncidence.nativeIso_inv_preimage
