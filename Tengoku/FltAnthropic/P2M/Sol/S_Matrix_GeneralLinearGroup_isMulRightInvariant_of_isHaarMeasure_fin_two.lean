import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure

namespace SolGL2HaarUnimodular

/--
@isnad1 id=eq.0h3v.s9.00a550ec2bbe from=translated src=- shape=2a7217e7 vocab=c0dc3cec
-/
theorem map_mul_right_eq_self
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] (g : GL (Fin 2) F) :
    Measure.map (· * g) μ = μ := by

  rw [isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor μ g]
  have hΔ : modularCharacterFun g = 1 :=
    Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one g
  rw [hΔ, one_smul]

end SolGL2HaarUnimodular

/--
@isnad1 id=ismulrig.0h2v.s9.2ae27e3c8120 from=translated src=- shape=be47e0c0 vocab=b4da4333
-/
theorem solution
    {F : Type*} [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant :=
  ⟨fun g => SolGL2HaarUnimodular.map_mul_right_eq_self μ g⟩
