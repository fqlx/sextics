import Proposal.GeometricLiteralAmbientCharts
import Proposal.GeometricAffineHigherChartRestriction
import Proposal.GeometricAffineHTwo
import Proposal.GeometricAffineHThree

/-!
# Cohomology on the four affine charts of the fixed threefold

Properness over the complex point makes intersections of the coordinate
charts affine. The additive structure sheaf on these intersections has
vanishing derived cohomology in the three degrees needed for the top
Čech comparison.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAmbientAffineCohomology

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralAmbientCharts CycleQ2LiteralAmbientSmooth CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricAffineHTwo

abbrev O := structureAdditiveSheaf (IncidenceFiber 57)

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology (IncidenceFiber 57))
    AddCommGrpCat.{0}) := HasExt.standard _

theorem fixedOpen_affine (i : Fin 4) : IsAffineOpen (fixedOpen i) :=
  .of_isIso (fixedChart i).inv

theorem inf_affine {U V : (IncidenceFiber 57).Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  let f := incidenceFiberToComplex 57
  let : IsProper f := incidenceFiber_proper 57
  exact (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
    U (by simp) V (by simp) hU hV

theorem pair_affine (i j : Fin 4) : IsAffineOpen (fixedOpen i ⊓ fixedOpen j) :=
  inf_affine (fixedOpen_affine i) (fixedOpen_affine j)

theorem triple_affine (i j k : Fin 4) : IsAffineOpen (fixedOpen i ⊓ fixedOpen j ⊓ fixedOpen k) :=
  inf_affine (pair_affine i j) (fixedOpen_affine k)

theorem HOne {U : (IncidenceFiber 57).Opens} (hU : IsAffineOpen U) : Subsingleton (O.H' 1 U) :=
  affineFrameHOne_subsingleton (A := Γ(IncidenceFiber 57, U)) hU.isoSpec O (Iso.refl _)

theorem HTwo {U : (IncidenceFiber 57).Opens} (hU : IsAffineOpen U) : Subsingleton (O.H' 2 U) :=
  affineFrameHTwo_subsingleton (A := Γ(IncidenceFiber 57, U)) hU.isoSpec O (Iso.refl _)
    (affine_H_two_subsingleton _)

theorem HThree {U : (IncidenceFiber 57).Opens} (hU : IsAffineOpen U) : Subsingleton (O.H' 3 U) :=
  CycleQ2GeometricAffineHThree.affineOpenHThree_subsingleton hU

end CycleQ2LiteralAmbientAffineCohomology
end

#print axioms CycleQ2LiteralAmbientAffineCohomology.triple_affine
#print axioms CycleQ2LiteralAmbientAffineCohomology.HTwo

#print axioms CycleQ2LiteralAmbientAffineCohomology.HThree
