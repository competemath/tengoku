import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure

namespace SolGL2HaarRightInv

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
  [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
  (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure]

/--
@isnad1 id=eq.0h3v.s9.00a550ec2bbe from=translated src=- shape=2a7217e7 vocab=c0dc3cec
-/
theorem map_mul_right_eq_self' (g : GL (Fin 2) F) : Measure.map (· * g) μ = μ := by
  rw [isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor μ g]
  have : modularCharacterFun g = 1 := Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one g
  rw [this, one_smul]

/--
@isnad1 id=ismulrig.0h2v.s9.69ad1f02fbd4 from=translated src=- shape=78fb2e85 vocab=2242c55b
-/
theorem isMulRightInvariant : μ.IsMulRightInvariant :=
  ⟨fun g => map_mul_right_eq_self' μ g⟩

/--
@isnad1 id=isinvinv.0h2v.s9.bf2ca5fc4357 from=translated src=- shape=78fb2e85 vocab=46bc2813
-/
theorem isInvInvariant : μ.IsInvInvariant := by
  haveI := isMulRightInvariant μ
  constructor
  let c : ENNReal := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts (GL (Fin 2) F) := Classical.arbitrary _
  have h3 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h4 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  rw [hc, h5, one_smul]

end SolGL2HaarRightInv

/--
@isnad1 id=and.0h2v.s9.aa4380bed702 from=translated src=- shape=07490018 vocab=58776766
-/
theorem solution
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant :=
  ⟨SolGL2HaarRightInv.isMulRightInvariant μ, SolGL2HaarRightInv.isInvInvariant μ⟩
