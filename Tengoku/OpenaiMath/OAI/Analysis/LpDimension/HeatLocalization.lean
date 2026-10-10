import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.SpectralProjection

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uE uV

namespace SubpolynomialLp

section GraphHeat
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

end GraphHeat

section LocalizationIntegral
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]

lemma sum_abs_outer_le (μ : V → ℝ) (w : E → ℝ) (z : E → V → ℝ)
    (hμ : ∀ v, 0 ≤ μ v) (hw : ∀ e, 0 ≤ w e) :
    (∑ e, ∑ f, w e * w f * |∑ v, μ v * z e v * z f v|) ≤
      ∑ v, μ v * (∑ e, w e * |z e v|)^2 := by
  calc
    _ ≤ ∑ e, ∑ f, ∑ v, μ v * (w e * |z e v|) * (w f * |z f v|) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      calc
        _ ≤ w e * w f * ∑ v, |μ v * z e v * z f v| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg (hw e) (hw f))
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          rw [abs_mul, abs_mul, abs_of_nonneg (hμ v)]
          ring
    _ = _ := by
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext f; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      simp only [sq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      ring

lemma localization_integral_bound (Q : E → E → ℝ) (F : ℝ → E → E → ℝ)
    (I : ℝ → V → ℝ) (μ : V → ℝ) (w : E → ℝ) (S : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hrep : ∀ e f, Q e f = 2 * ∫ t in Set.Ioi (0 : ℝ), F t e f)
    (hiF : ∀ e f, IntegrableOn (fun t => F t e f) (Set.Ioi 0))
    (hiI : ∀ v, IntegrableOn (fun t => I t v) (Set.Ioi 0))
    (hint : ∀ v, (∫ t in Set.Ioi (0 : ℝ), I t v) = Real.log (1 / μ v))
    (hb : ∀ t : ℝ, 0 < t →
      (∑ e, ∑ f, w e * w f * |F t e f|) ≤ S * ∑ v, μ v * I t v) :
    (∑ e, ∑ f, w e * w f * |Q e f|) ≤
      2 * S * ∑ v, μ v * Real.log (1 / μ v) := by
  have hiF' (e f : E) : IntegrableOn (fun t => w e * w f * |F t e f|) (Set.Ioi 0) :=
    (hiF e f).abs.const_mul _
  have hsumF : IntegrableOn (fun t => ∑ e, ∑ f, w e * w f * |F t e f|) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun e _ => integrable_finsetSum _ (fun f _ => hiF' e f))
  have hsumI : IntegrableOn (fun t => ∑ v, μ v * I t v) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun v _ => (hiI v).const_mul _)
  calc
    _ ≤ 2 * (∑ e, ∑ f, w e * w f * ∫ t in Set.Ioi (0 : ℝ), |F t e f|) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      rw [hrep, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hh := mul_le_mul_of_nonneg_left
        (abs_integral_le_integral_abs (f := fun t => F t e f) (μ := volume.restrict (Set.Ioi 0)))
        (mul_nonneg (hw e) (hw f))
      nlinarith
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), ∑ e, ∑ f, w e * w f * |F t e f| := by
      congr 1
      rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ (fun f _ => hiF' e f))]
      apply Finset.sum_congr rfl
      intro e _
      rw [integral_finsetSum _ (fun f _ => hiF' e f)]
      simp only [integral_const_mul]
    _ ≤ 2 * ∫ t in Set.Ioi (0 : ℝ), S * ∑ v, μ v * I t v := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply integral_mono_ae hsumF (hsumI.const_mul S)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb t ht
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun v _ => (hiI v).const_mul _)]
      simp only [integral_const_mul, hint, mul_assoc]

end LocalizationIntegral

end SubpolynomialLp

end

end OAI
