import Tengoku.Piirrationalitymeasure.Formalization.ContourEstimate
import Tengoku.Seed.Analysis.SpecialFunctions.Log.ENNRealLog

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Lemma 4.4, including the extended-real convention for vanishing integrals. -/

namespace PiIrrationality

open Filter
open scoped Topology

/--
@isnad1 id=iff.0h1v.s4.53d971517d53 from=translated src=- shape=26779bf1 vocab=e91b7841
-/
theorem log_norm_eq_bot_iff (z : ℂ) :
    ENNReal.log (ENNReal.ofReal ‖z‖) = ⊥ ↔ z = 0 := by
  simp

/--
@isnad1 id=le.3h4v.s7.edb6e60b176d from=translated src=- shape=2ee4b710 vocab=36a841bf
-/
theorem log_norm_limsup_of_exp_bound {J : ℕ → ℂ} {N C s : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n : ℕ in atTop, ‖J n‖ ≤ C * Real.exp (N * n * s)) :
    limsup (fun n : ℕ => ENNReal.log (ENNReal.ofReal ‖J n‖) /
      ((N * n : ℝ) : EReal)) atTop ≤ (s : EReal) := by
  have hCpos : 0 < C + 1 := by linarith
  have hupper : ∀ᶠ n : ℕ in atTop,
      ENNReal.log (ENNReal.ofReal ‖J n‖) / ((N * n : ℝ) : EReal) ≤
        ((s + Real.log (C + 1) / (N * n) : ℝ) : EReal) := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hden : 0 < N * (n : ℝ) := mul_pos hN hnR
    have hlarge : ‖J n‖ ≤ (C + 1) * Real.exp (N * n * s) :=
      hn.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
    have hlog := ENNReal.log_le_log (ENNReal.ofReal_le_ofReal hlarge)
    rw [ENNReal.log_ofReal_of_pos (mul_pos hCpos (Real.exp_pos _)),
      Real.log_mul hCpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have hdiv := EReal.div_le_div_right_of_nonneg
      (show (0 : EReal) ≤ ((N * n : ℝ) : EReal) by exact_mod_cast hden.le) hlog
    have heq : (Real.log (C + 1) + N * n * s) / (N * n) =
        s + Real.log (C + 1) / (N * n) := by field_simp; ring
    simpa only [← EReal.coe_div, heq] using hdiv
  have hd : Tendsto (fun n : ℕ => N * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hN
  have hz : Tendsto (fun n : ℕ => Real.log (C + 1) / (N * n)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hd
  have hlim : Tendsto (fun n : ℕ => s + Real.log (C + 1) / (N * n))
      atTop (𝓝 s) := by simpa only [add_zero] using hz.const_add s
  calc
    _ ≤ limsup (fun n : ℕ => ((s + Real.log (C + 1) / (N * n) : ℝ) : EReal)) atTop :=
      limsup_le_limsup hupper
        (isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
        ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
    _ = _ := (EReal.tendsto_coe.mpr hlim).limsup_eq

/--
@isnad1 id=le.6h7v.s9.42fb5ed61a7b from=translated src=- shape=55b42eb7 vocab=9ddfbce7
-/
theorem lemma_4_4_exp_bound {tau : ℝ → ℂ} {f : ℕ → ℂ → ℂ}
    {A : ℝ → ℝ} {phi : ℂ → ℝ} {N s : ℝ} (hN : 0 ≤ N)
    (hA : IntervalIntegrable (fun t => A t * ‖deriv tau t‖) MeasureTheory.volume 0 1)
    (hAnonneg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ A t)
    (hphi : ∀ t ∈ Set.Ioc (0 : ℝ) 1, phi (tau t) ≤ s)
    (hbound : ∀ n : ℕ, 0 < n → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖f n (tau t)‖ ≤ A t * Real.exp (N * n * phi (tau t)))
    (n : ℕ) (hn : 0 < n) :
    ‖∫ t in (0 : ℝ)..1, f n (tau t) * deriv tau t‖ ≤
      Real.exp (N * n * s) * ∫ t in (0 : ℝ)..1, A t * ‖deriv tau t‖ := by
  have hmajor : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖f n (tau t) * deriv tau t‖ ≤
        (A t * ‖deriv tau t‖) * Real.exp (N * n * s) := by
    intro t ht
    have hexp := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hphi t ht) (mul_nonneg hN (Nat.cast_nonneg n)))
    calc
      _ ≤ (A t * Real.exp (N * n * phi (tau t))) * ‖deriv tau t‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound n hn t ht) (norm_nonneg _)
      _ ≤ (A t * Real.exp (N * n * s)) * ‖deriv tau t‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (hAnonneg t ht))
          (norm_nonneg _)
      _ = _ := by ring
  have h := intervalIntegral_norm_bound (hA.mul_const (Real.exp (N * n * s))) hmajor
  rw [intervalIntegral.integral_mul_const, mul_comm] at h
  exact h

/--
@isnad1 id=le.5h6v.s8.5986d58544d6 from=translated src=- shape=4dea5162 vocab=37cb6918
-/
theorem lemma_4_4_log_limsup {tau : ℝ → ℂ} {f : ℕ → ℂ → ℂ}
    {A : ℝ → ℝ} {phi : ℂ → ℝ} {N s : ℝ} (hN : 0 < N)
    (hA : IntervalIntegrable (fun t => A t * ‖deriv tau t‖) MeasureTheory.volume 0 1)
    (hAnonneg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ A t)
    (hphi : ∀ t ∈ Set.Ioc (0 : ℝ) 1, phi (tau t) ≤ s)
    (hbound : ∀ n : ℕ, 0 < n → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖f n (tau t)‖ ≤ A t * Real.exp (N * n * phi (tau t))) :
    limsup (fun n : ℕ =>
      ENNReal.log (ENNReal.ofReal ‖∫ t in (0 : ℝ)..1, f n (tau t) * deriv tau t‖) /
        ((N * n : ℝ) : EReal)) atTop ≤ (s : EReal) := by
  have hC : 0 ≤ ∫ t in (0 : ℝ)..1, A t * ‖deriv tau t‖ := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (hAnonneg t ht) (norm_nonneg _)
  apply log_norm_limsup_of_exp_bound hN hC
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simpa only [mul_comm] using lemma_4_4_exp_bound hN.le hA hAnonneg hphi hbound n hn

end PiIrrationality
