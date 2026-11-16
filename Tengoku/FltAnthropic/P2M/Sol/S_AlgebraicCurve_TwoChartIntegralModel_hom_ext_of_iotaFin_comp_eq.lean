import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace PinsBody

/--
@isnad1 id=isdomina.0h3v.s6.fb67f3b1e5aa from=translated src=- shape=80f8fe29 vocab=880d228c
-/
theorem isDominant_ιFin (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    IsDominant (ιFin R F j) := by
  haveI := TwoChartIntegralModel.isIntegral R F j
  exact ⟨(ιFin R F j).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/--
@isnad1 id=eq.2h8v.s7.a17db12b3d5d from=translated src=- shape=cc6993d0 vocab=d7526d0b
-/
theorem hom_ext (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g := by
  haveI := TwoChartIntegralModel.isIntegral R F j
  haveI := isDominant_ιFin R F j
  exact ext_of_isDominant_of_isSeparated q h (ιFin R F j) hFin

end PinsBody

/--
@isnad1 id=eq.2h8v.s7.a17db12b3d5d from=translated src=- shape=cc6993d0 vocab=d7526d0b
-/
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g :=
  PinsBody.hom_ext R F j f g q h hFin

