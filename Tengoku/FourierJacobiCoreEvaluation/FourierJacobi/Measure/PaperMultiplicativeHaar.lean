import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Measure.MultiplicativeHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The source's multiplicative Haar normalization

The source uses d×a = |a|⁻¹ da, so the volume of O_K^× is
1-q⁻¹. The auxiliary `multiplicativeHaar` has unit volume one; the
measure here restores the source normalization exactly once.
-/

noncomputable section

open MeasureTheory ValuativeRel
open scoped ENNReal

namespace FourierJacobi.Measure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/--
@isnad1 id=lt.0h1v.s5.88fc7ee5a884 from=translated src=- shape=f600addd vocab=8d47aff1
-/
theorem paperMultiplicativeFactor_pos : 0 < 1 - (residueCardinality K : ℝ)⁻¹ := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  exact sub_pos.mpr ((inv_lt_one₀ (lt_trans zero_lt_one hq)).mpr hq)

variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]

/-- The paper's multiplicative measure: unit-shell mass 1-q⁻¹.-/
def paperMultiplicativeHaar : MeasureTheory.Measure Kˣ :=
  ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) • multiplicativeHaar K

/--
@isnad1 id=ishaarme.0h1v.s6.bfb53dd84752 from=translated src=- shape=61cb5b0b vocab=d25ca5fd
-/
instance paperMultiplicativeHaar_isHaarMeasure : (paperMultiplicativeHaar K).IsHaarMeasure := by
  unfold paperMultiplicativeHaar
  exact Measure.IsHaarMeasure.smul (multiplicativeHaar K)
    (ENNReal.ofReal_pos.mpr (paperMultiplicativeFactor_pos K)).ne'
    ENNReal.ofReal_ne_top

/--
@isnad1 id=eq.0h1v.s7.fecdb574ae7a from=translated src=- shape=8a0176a2 vocab=fc0daee0
-/
theorem paperMultiplicativeHaar_valuationRingUnits :
    paperMultiplicativeHaar K (valuationRingUnits K : Set Kˣ) =
      ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) := by
  simp only [paperMultiplicativeHaar, Measure.smul_apply,
    multiplicativeHaar_valuationRingUnits, smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h2v.s7.c8eb81cde6bf from=translated src=- shape=2c2e7178 vocab=a3355b4c
-/
theorem paperMultiplicativeHaar_unitValuationShell (n : ℤ) :
    paperMultiplicativeHaar K (unitValuationShell K n) =
      ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) := by
  simp only [paperMultiplicativeHaar, Measure.smul_apply,
    multiplicativeHaar_unitValuationShell, smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h2v.s6.0c23eba6e4bd from=translated src=- shape=c37613a5 vocab=591c8dc2
-/
theorem paperMultiplicativeHaar_real_unitValuationShell (n : ℤ) :
    (paperMultiplicativeHaar K).real (unitValuationShell K n) =
      1 - (residueCardinality K : ℝ)⁻¹ := by
  rw [Measure.real, paperMultiplicativeHaar_unitValuationShell,
    ENNReal.toReal_ofReal (paperMultiplicativeFactor_pos K).le]

end FourierJacobi.Measure
