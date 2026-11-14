import Tengoku.Piirrationalitymeasure.Formalization.EndpointIndexGeometry
import Tengoku.Piirrationalitymeasure.Formalization.SavingTranslationBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A fixed cut outside the endpoint set and translation-invariance of period integrals. -/

namespace PiIrrationality

open MeasureTheory Set

theorem translatedSavingChi_periodic (a b c : ℤ) (z : ℝ × ℝ) :
    Function.Periodic (translatedSavingChi a b c z) 1 := by
  intro u
  unfold translatedSavingChi
  convert savingChi_add_int ((a : ℝ) * u + z.1) ((b : ℝ) * u + z.2)
    ((c : ℝ) * u) a b c using 1 <;> congr 1 <;> ring

theorem translatedSavingMeasure_eq_period (a b c : ℤ) (z : ℝ × ℝ) (cut : ℝ) :
    translatedSavingMeasure a b c z =
      ∫ u in cut..cut + 1, translatedSavingChi a b c z u := by
  simpa only [translatedSavingMeasure, zero_add] using
    (translatedSavingChi_periodic a b c z).intervalIntegral_add_eq 0 cut

def candidateEndpointCut : ℚ := -1 / 11140

theorem savingEndpoint_candidate_cut_bounds (T : SavingEndpointType) {z : ℝ × ℝ}
    (hz : parameterNormOne z ≤ 1 / 100) :
    (candidateEndpointStart T : ℝ) - 1 <
        savingEndpointArgument 1857 3714 5570 z T candidateEndpointCut ∧
      savingEndpointArgument 1857 3714 5570 z T candidateEndpointCut <
        (candidateEndpointStart T : ℝ) := by
  have hx : |z.1| ≤ 1 / 100 := by
    dsimp [parameterNormOne] at hz
    linarith [abs_nonneg z.2]
  have hy : |z.2| ≤ 1 / 100 := by
    dsimp [parameterNormOne] at hz
    linarith [abs_nonneg z.1]
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hy
  cases T <;> dsimp [candidateEndpointStart, savingEndpointArgument,
    savingEndpointSlope, savingEndpointShift, candidateEndpointCut] <;>
    norm_num <;> constructor <;> linarith

theorem savingEndpoint_candidate_period_enumeration (T : SavingEndpointType) (j : ℤ)
    {z : ℝ × ℝ} (hz : parameterNormOne z ≤ 1 / 100) :
    savingEndpoint 1857 3714 5570 z T j ∈
      Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1) ↔
        j ∈ candidateEndpointIndices T := by
  have hm : 0 < savingEndpointSlope 1857 3714 5570 T := by
    cases T <;> norm_num [savingEndpointSlope]
  have hsize : savingEndpointSlope 1857 3714 5570 T = (candidateEndpointSize T : ℝ) := by
    cases T <;> norm_num [savingEndpointSlope, candidateEndpointSize]
  obtain ⟨hlo, hhi⟩ := savingEndpoint_candidate_cut_bounds T hz
  have he := (savingEndpoint_eq_iff hm.ne').mp
    (rfl : savingEndpoint 1857 3714 5570 z T j = savingEndpoint 1857 3714 5570 z T j)
  dsimp [savingEndpointArgument] at hlo hhi
  rw [mem_candidateEndpointIndices, mem_Ioo]
  constructor
  · rintro ⟨hl, hr⟩
    have hml := mul_lt_mul_of_pos_left hl hm
    have hmr := mul_lt_mul_of_pos_left hr hm
    have hjlo : (candidateEndpointStart T : ℝ) - 1 < (j : ℝ) := by linarith
    have hjhi : (j : ℝ) < (candidateEndpointStart T : ℝ) + (candidateEndpointSize T : ℝ) := by
      rw [hsize] at hmr he hlo hhi
      nlinarith only [hmr, he, hhi]
    have hjlo' : candidateEndpointStart T - 1 < j := by exact_mod_cast hjlo
    have hjhi' : j < candidateEndpointStart T + (candidateEndpointSize T : ℤ) := by
      exact_mod_cast hjhi
    omega
  · rintro ⟨hl, hr⟩
    have hr' : j ≤ candidateEndpointStart T + (candidateEndpointSize T : ℤ) - 1 := by omega
    have hlj : (candidateEndpointStart T : ℝ) ≤ (j : ℝ) := by exact_mod_cast hl
    have hrj : (j : ℝ) ≤ (candidateEndpointStart T : ℝ) +
        (candidateEndpointSize T : ℝ) - 1 := by exact_mod_cast hr'
    constructor
    · apply (mul_lt_mul_iff_right₀ hm).mp
      linarith only [he, hhi, hlj]
    · apply (mul_lt_mul_iff_right₀ hm).mp
      rw [hsize] at he hlo ⊢
      nlinarith only [he, hlo, hrj]

end PiIrrationality
