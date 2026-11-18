import Proposal.GeometricFamilyDeformation

/-!
# Comparing unit lifts on the original square-zero overlap

The coefficient of a unit reducing to one is additive under multiplication.
Consequently, changing the three lifted transitions on a face changes
their obstruction by exactly the alternating boundary of the three
edge corrections. This works for arbitrary lifts, including those
obtained by restricting a coordinate-chart projector to a pivot chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2ProjectorTransitionComparison
open CycleQ2GeometricProjectorDefect
variable {E R : Type*} [CommRing E] [CommRing R] {ρ : E →+* R} (K : Coefficients ρ)

abbrev reduceUnit (ρ : E →+* R) : Eˣ →* Rˣ := Units.map ρ.toMonoidHom
abbrev unitKernel (ρ : E →+* R) := (reduceUnit ρ).ker

private theorem kernel_sub (u : unitKernel ρ) : ρ ((u.val : E) - 1) = 0 := by
  have he : reduceUnit ρ u.val = 1 := u.property
  rw [map_sub, map_one, show ρ (u.val : E) = 1 from congrArg Units.val he, sub_self]

/-- The additive E-to-R kernel coefficient, as a homomorphism on the unit kernel. -/
def kernelLog : unitKernel ρ →* Multiplicative R where
  toFun u := Multiplicative.ofAdd (K.coefficient ((u.val : E) - 1) (kernel_sub u))
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply K.injective
    rw [Coefficients.epsilon_coefficient, map_zero]
    exact sub_self 1
  map_mul' u v := by
    apply congrArg Multiplicative.ofAdd
    apply K.injective
    simp only [Multiplicative.toAdd_ofAdd]
    rw [map_add, Coefficients.epsilon_coefficient, Coefficients.epsilon_coefficient, Coefficients.epsilon_coefficient]
    have hz := K.epsilon_mul_epsilon (K.coefficient ((u.val : E) - 1) (kernel_sub u))
      (K.coefficient ((v.val : E) - 1) (kernel_sub v))
    rw [Coefficients.epsilon_coefficient, Coefficients.epsilon_coefficient] at hz
    change (u.val : E) * (v.val : E) - 1 = _ + _
    linear_combination hz

theorem epsilon_kernelLog (u : unitKernel ρ) :
    K.epsilon (kernelLog K u).toAdd = (u.val : E) - 1 := K.epsilon_coefficient _ (kernel_sub u)

def face (u v w : Eˣ) (h : reduceUnit ρ u * reduceUnit ρ v = reduceUnit ρ w) : unitKernel ρ :=
  ⟨u * v * w⁻¹, by change reduceUnit ρ _ = 1; rw [map_mul, map_mul, map_inv, h, mul_inv_cancel]⟩

def edge (u v : Eˣ) (h : reduceUnit ρ u = reduceUnit ρ v) : unitKernel ρ :=
  ⟨u * v⁻¹, by change reduceUnit ρ _ = 1; rw [map_mul, map_inv, h, mul_inv_cancel]⟩

theorem face_change (u v w u' v' w' : Eˣ)
    (h : reduceUnit ρ u * reduceUnit ρ v = reduceUnit ρ w)
    (hu : reduceUnit ρ u = reduceUnit ρ u') (hv : reduceUnit ρ v = reduceUnit ρ v')
    (hw : reduceUnit ρ w = reduceUnit ρ w') :
    (kernelLog K (face u v w h)).toAdd -
        (kernelLog K (face u' v' w' (hu ▸ hv ▸ hw ▸ h))).toAdd =
      (kernelLog K (edge v v' hv)).toAdd - (kernelLog K (edge w w' hw)).toAdd +
        (kernelLog K (edge u u' hu)).toAdd := by
  have he : face u v w h * (face u' v' w' (hu ▸ hv ▸ hw ▸ h))⁻¹ =
      edge v v' hv * (edge w w' hw)⁻¹ * edge u u' hu := by
    apply Subtype.ext
    change (u * v * w⁻¹) * (u' * v' * w'⁻¹)⁻¹ = (v * v'⁻¹) * (w * w'⁻¹)⁻¹ * (u * u'⁻¹)
    group <;> ac_rfl
  have he' := congrArg (kernelLog K) he
  simp only [map_mul, map_inv] at he'
  exact (by simpa only [sub_eq_add_neg, Multiplicative.toAdd_mul, Multiplicative.toAdd_inv] using congrArg Multiplicative.toAdd he')

/-- Edge corrections restrict and specialize with every map respecting epsilon. -/
theorem kernelLog_map {E' R' : Type*} [CommRing E'] [CommRing R'] {ρ' : E' →+* R'}
    (K' : Coefficients ρ') (f : E →+* E') (g : R →+* R')
    (hε : ∀ x, f (K.epsilon x) = K'.epsilon (g x))
    (u : unitKernel ρ) (v : unitKernel ρ') (h : (v.val : E') = f (u.val : E)) :
    (kernelLog K' v).toAdd = g (kernelLog K u).toAdd := by
  apply K'.injective
  change K'.epsilon (K'.coefficient ((v.val : E') - 1) (kernel_sub v)) =
    K'.epsilon (g (K.coefficient ((u.val : E) - 1) (kernel_sub u)))
  rw [Coefficients.epsilon_coefficient, ← hε, Coefficients.epsilon_coefficient, map_sub, map_one, h]

end CycleQ2ProjectorTransitionComparison
end

#print axioms CycleQ2ProjectorTransitionComparison.face_change
#print axioms CycleQ2ProjectorTransitionComparison.kernelLog_map
