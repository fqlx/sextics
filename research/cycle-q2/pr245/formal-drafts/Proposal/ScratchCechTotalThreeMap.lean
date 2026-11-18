import Proposal.ScratchCechDeRhamTotalThree

/-! Functoriality of degree-three total cohomology for maps which commute
with restrictions and with the exterior differential. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2CechDeRhamTotalThree
universe u v
variable {B : Double.{u}} {C : Double.{v}}

structure DoubleMap (B : Double.{u}) (C : Double.{v}) where
  app : ∀ p q, B.X p q →+ C.X p q
  horizontal : ∀ p q x, app (p+1) q (B.h p q x) = C.h p q (app p q x)
  vertical : ∀ p q x, app p (q+1) (B.v p q x) = C.v p q (app p q x)

namespace DoubleMap
variable (f : DoubleMap B C)

def inTwo : Two B →+ Two C :=
  (f.app 0 2).prodMap ((f.app 1 1).prodMap (f.app 2 0))

def inThree : Three B →+ Three C :=
  (f.app 0 3).prodMap ((f.app 1 2).prodMap ((f.app 2 1).prodMap (f.app 3 0)))

def inFour : Four B →+ Four C :=
  (f.app 0 4).prodMap ((f.app 1 3).prodMap ((f.app 2 2).prodMap ((f.app 3 1).prodMap (f.app 4 0))))

theorem map_d2 (x : Two B) : f.inThree (d2 B x) = d2 C (f.inTwo x) := by
  simp [inThree,inTwo,d2,AddMonoidHom.prodMap,f.horizontal,f.vertical]

theorem map_d3 (z : Three B) : f.inFour (d3 B z) = d3 C (f.inThree z) := by
  simp [inFour,inThree,d3,AddMonoidHom.prodMap,f.horizontal,f.vertical]

def onCycles : Cycles B →+ Cycles C :=
  (f.inThree.comp (Cycles B).subtype).codRestrict (Cycles C) (by
    intro z
    change d3 C (f.inThree z.1) = 0
    rw [← f.map_d3, show d3 B z.1 = 0 from z.2, map_zero])

def onCohomology : HThree B →+ HThree C :=
  QuotientAddGroup.lift _ ((classOf C).comp f.onCycles) (by
    rintro z ⟨x,rfl⟩
    apply (classOf_eq_zero C _).mpr
    exact ⟨f.inTwo x,(f.map_d2 x).symm⟩)

@[simp] theorem onCohomology_classOf (z : Cycles B) :
    f.onCohomology (classOf B z) = classOf C (f.onCycles z) := rfl

end DoubleMap
end CycleQ2CechDeRhamTotalThree
end
#print axioms CycleQ2CechDeRhamTotalThree.DoubleMap.onCohomology
