import Proposal.GeometricFamilyDeformation

/-!
# Transport of rank-one projector obstruction scalars

A ring map preserving the epsilon coefficients carries the defect of three
lifted projectors to the defect of their images. The resulting scalar on
the rank-one image commutes with specialization of the original matrix
and of the certificate for its entries.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2ProjectorCochainSpecialization

open CycleQ2GeometricProjectorDefect CycleQ2GeometricRankOneImage

variable {E E' R R' I : Type*} [CommRing E] [CommRing E'] [CommRing R] [CommRing R']
  {ρ : E →+* R} {ρ' : E' →+* R'} (K : Coefficients ρ) (K' : Coefficients ρ')
  (f : E →+* E') (g : R →+* R') (hε : ∀ x, f (K.epsilon x) = K'.epsilon (g x))

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  (M : Matrix m n R) (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
  (w : I → m × n → R) (hw : ∀ i, ∑ q, w i q * M q.1 q.2 = 1)
  (e : I → Matrix m m E) (hr : ∀ i, ρ.mapMatrix (e i) = projectorMatrix M (w i))
  (M' : Matrix m n R') (hM' : ∀ i j k l, M' i j * M' k l = M' k j * M' i l)
  (w' : I → m × n → R') (hw' : ∀ i, ∑ q, w' i q * M' q.1 q.2 = 1)
  (e' : I → Matrix m m E') (hr' : ∀ i, ρ'.mapMatrix (e' i) = projectorMatrix M' (w' i))

include hε

/-- The exact epsilon coefficient of the specialized defect, before taking its rank-one scalar. -/
theorem imageCoefficient_map (he : ∀ i, (e i).map f = e' i) (i j k : I) :
    (imageCoefficient ρ (K.matrixCoefficients m) M hM w hw e hr i j k).map g =
      imageCoefficient ρ' (K'.matrixCoefficients m) M' hM' w' hw' e' hr' i j k := by
  apply (K'.matrixCoefficients m).injective
  let d := imageCoefficient ρ (K.matrixCoefficients m) M hM w hw e hr i j k
  have h₁ : (K'.matrixCoefficients m).epsilon (d.map g) = ((K.matrixCoefficients m).epsilon d).map f := by
    ext a b
    exact (hε (d a b)).symm
  rw [h₁]
  change (((K.matrixCoefficients m).epsilon ((K.matrixCoefficients m).cochain e _ i j k)).map f) =
    (K'.matrixCoefficients m).epsilon ((K'.matrixCoefficients m).cochain e' _ i j k)
  rw [Coefficients.epsilon_cochain, Coefficients.epsilon_cochain]
  change f.mapMatrix (e i * e j * e k - e i * e k) = _
  simp only [map_sub, map_mul]
  change (e i).map f * (e j).map f * (e k).map f - (e i).map f * (e k).map f = _
  rw [he,he,he]
  rfl

theorem scalarCochain_map (hmat : M.map g = M') (he : ∀ i, (e i).map f = e' i)
    (v : m × n → R) (i j k : I) :
    g (scalarCochain ρ (K.matrixCoefficients m) M hM w hw e hr v i j k) =
      scalarCochain ρ' (K'.matrixCoefficients m) M' hM' w' hw' e' hr' (fun q => g (v q)) i j k := by
  rw [scalarCochain, matrixScalar_map, hmat, imageCoefficient_map K K' f g hε M hM w hw e hr M' hM' w' hw' e' hr' he]
  rfl

end CycleQ2ProjectorCochainSpecialization
end

#print axioms CycleQ2ProjectorCochainSpecialization.scalarCochain_map
