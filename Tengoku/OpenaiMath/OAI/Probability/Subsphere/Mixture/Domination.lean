import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.Subsphere.Mixture.Latitude

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

private def betaRaw (a b x : ℝ) : ℝ≥0∞ :=
  if 0 < x ∧ x < 1 then ENNReal.ofReal (x ^ (a - 1) * (1 - x) ^ (b - 1)) else 0

private lemma betaRaw_eq (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    betaRaw a b x = ENNReal.ofReal (beta a b) * betaPDF a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaRaw, betaPDF, betaPDFReal, ite_eq_left hx]
    rw [← ENNReal.ofReal_mul (beta_pos ha hb).le]
    congr 1
    field_simp [(beta_pos ha hb).ne']
  · simp [betaRaw, betaPDF, betaPDFReal, hx]

private lemma lintegral_betaRaw (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, betaRaw a b x = ENNReal.ofReal (beta a b) := by
  simp_rw [betaRaw_eq a b _ ha hb]
  rw [lintegral_const_mul' _ _]
  · simp [lintegral_betaPDF_eq_one ha hb]
  · exact ENNReal.ofReal_ne_top

lemma beta_antitone_left {a A b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ A) :
    beta A b ≤ beta a b := by
  apply (ENNReal.ofReal_le_ofReal_iff (beta_pos ha hb).le).1
  rw [← lintegral_betaRaw A b (lt_of_lt_of_le ha h) hb, ← lintegral_betaRaw a b ha hb]
  apply lintegral_mono
  intro x
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaRaw, ite_eq_left hx]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le (by linarith)
  · simp [betaRaw, hx]

lemma beta_antitone_right {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ≤ B) :
    beta a B ≤ beta a b := by
  have hcomm (u v : ℝ) : beta u v = beta v u := by unfold beta; rw [mul_comm, add_comm]
  rw [hcomm a B, hcomm a b]
  exact beta_antitone_left hb ha h

private lemma rpow_decrease_shift {x a A D : ℝ} (hx : (1 / 2 : ℝ) ≤ x)
    (ha : a ≤ A) (hD : A - a ≤ D) :
    x ^ (a - 1) ≤ (2 : ℝ) ^ D * x ^ (A - 1) := by
  have hx0 : 0 < x := by linarith
  have hfactor : x ^ (a - A) ≤ (2 : ℝ) ^ D := by
    calc
      x ^ (a - A) ≤ (1 / 2 : ℝ) ^ (a - A) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)
      _ = (2 : ℝ) ^ (A - a) := by
        rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ D := Real.rpow_le_rpow_of_exponent_le (by norm_num) hD
  calc
    x ^ (a - 1) = x ^ (a - A) * x ^ (A - 1) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ D * x ^ (A - 1) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hx0.le _)

lemma betaPDFReal_domination_right_half {a A b D x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : a ≤ A) (hD : A - a ≤ D)
    (hx : (1 / 2 : ℝ) ≤ x) :
    betaPDFReal a b x ≤ (2 : ℝ) ^ D * betaPDFReal A b x := by
  by_cases hx1 : x < 1
  · have hxx : 0 < x ∧ x < 1 := ⟨by linarith, hx1⟩
    simp only [betaPDFReal, ite_eq_left hxx]
    have hbeta : 1 / beta a b ≤ 1 / beta A b :=
      one_div_le_one_div_of_le (beta_pos (lt_of_lt_of_le ha hA) hb)
        (beta_antitone_left ha hb hA)
    have hp := rpow_decrease_shift hx hA hD
    have hxpow : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hxx.1.le _
    have hbpow : 0 ≤ (1 - x) ^ (b - 1) := Real.rpow_nonneg (by linarith) _
    calc
      _ ≤ ((1 / beta A b) * ((2 : ℝ) ^ D * x ^ (A - 1))) * (1 - x) ^ (b - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hbeta hp hxpow (le_of_lt (one_div_pos.2 (beta_pos (lt_of_lt_of_le ha hA) hb)))) hbpow
      _ = _ := by ring
  · have hxx : ¬ (0 < x ∧ x < 1) := by tauto
    simp [betaPDFReal, hxx]

lemma betaPDFReal_domination_left_half {a b B D x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : b ≤ B) (hD : B - b ≤ D)
    (hx : x ≤ (1 / 2 : ℝ)) :
    betaPDFReal a b x ≤ (2 : ℝ) ^ D * betaPDFReal a B x := by
  by_cases hxx : 0 < x ∧ x < 1
  · simp only [betaPDFReal, ite_eq_left hxx]
    have hbeta : 1 / beta a b ≤ 1 / beta a B :=
      one_div_le_one_div_of_le (beta_pos ha (lt_of_lt_of_le hb hB))
        (beta_antitone_right ha hb hB)
    have hp := rpow_decrease_shift (x := 1 - x) (by linarith) hB hD
    have hxpow : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hxx.1.le _
    have hbpow : 0 ≤ (1 - x) ^ (b - 1) := Real.rpow_nonneg (by linarith [hxx.2]) _
    calc
      _ ≤ ((1 / beta a B) * x ^ (a - 1)) * ((2 : ℝ) ^ D * (1 - x) ^ (B - 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hbeta hxpow) hp hbpow
          (mul_nonneg (le_of_lt (one_div_pos.2 (beta_pos ha (lt_of_lt_of_le hb hB)))) hxpow)
      _ = _ := by ring
  · simp [betaPDFReal, hxx]

theorem betaMeasure_two_component {a A b B D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : a ≤ A) (hB : b ≤ B)
    (hAD : A - a ≤ D) (hBD : B - b ≤ D) :
    betaMeasure a b ≤ ENNReal.ofReal ((2 : ℝ) ^ D) •
      (betaMeasure A b + betaMeasure a B) := by
  have hpdf : betaPDF a b ≤ fun x => ENNReal.ofReal ((2 : ℝ) ^ D) *
      (betaPDF A b x + betaPDF a B x) := by
    intro x
    rcases le_total (1 / 2 : ℝ) x with hx | hx
    · have h := betaPDFReal_domination_right_half ha hb hA hAD hx
      have hh := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_mul (by positivity)] at hh
      exact hh.trans (mul_le_mul' le_rfl (le_add_right le_rfl))
    · have h := betaPDFReal_domination_left_half ha hb hB hBD hx
      have hh := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_mul (by positivity)] at hh
      exact hh.trans (mul_le_mul' le_rfl (le_add_left le_rfl))
  have hm : Measurable (betaPDF A b) := (measurable_betaPDFReal A b).ennreal_ofReal
  unfold betaMeasure
  rw [← withDensity_add_left hm,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  exact withDensity_mono (Filter.Eventually.of_forall hpdf)

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory Set
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end

end OAI
