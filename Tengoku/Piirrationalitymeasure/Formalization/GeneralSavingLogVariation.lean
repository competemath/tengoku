import Tengoku.Piirrationalitymeasure.Formalization.SavingRadialModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Normalizing the general period estimate gives (6.20)--(6.21). -/

namespace PiIrrationality

theorem savingOmega_scaled_translation (a b : ℝ) {c : ℝ} (hc : 0 < c) (h : ℝ × ℝ) :
    savingOmega (a + c * h.1) (b + c * h.2) c =
      c * savingPhi ((a / c, b / c) + h) := by
  have he := savingOmega_eq_scaled_phi (((a / c, b / c) + h).1)
    (((a / c, b / c) + h).2) hc
  have hx : c * (((a / c, b / c) + h).1) = a + c * h.1 := by
    dsimp
    field_simp
  have hy : c * (((a / c, b / c) + h).2) = b + c * h.2 := by
    dsimp
    field_simp
  rw [hx, hy] at he
  exact he

namespace SavingRadialModel

theorem phi_log_variation {a b c : ℤ} (M : SavingRadialModel a b c)
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) (hc : 0 < (c : ℝ))
    (hq : (a : ℝ) + 2 * b - c ≠ 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ h ∈ M.domain,
      0 < parameterNormOne h → parameterNormOne h ≤ r →
      |savingPhi (((a : ℝ) / c, (b : ℝ) / c) + h) -
        savingPhi ((a : ℝ) / c, (b : ℝ) / c) -
        M.variation h * Real.log (1 / parameterNormOne h)| ≤ C * parameterNormOne h := by
  obtain ⟨r, C, hr, hC, hmodel⟩ := M.omega_log_variation ha hb hc.le hq
  have hB := M.bound_nonneg
  refine ⟨r / c, C + M.bound * |Real.log c|, by positivity, by positivity, ?_⟩
  intro h hmem hd hdr
  have hn : parameterNormOne ((c : ℝ) • h) = c * parameterNormOne h := by
    rw [parameterNormOne_smul, abs_of_pos hc]
  have hs : parameterNormOne ((c : ℝ) • h) ≤ r := by
    rw [hn]
    simpa only [mul_comm] using (le_div_iff₀ hc).mp hdr
  have hpos : 0 < parameterNormOne ((c : ℝ) • h) := by rw [hn]; positivity
  have he := hmodel ((c : ℝ) • h) (M.scale_mem h hmem c hc.le) hpos hs
  have hzero : savingOmega a b c = c * savingPhi ((a : ℝ) / c, (b : ℝ) / c) := by
    simpa only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] using
      savingOmega_scaled_translation a b hc 0
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hn,
    savingOmega_scaled_translation a b hc, hzero,
    M.variation_smul h hmem c hc.le] at he
  have hlog : Real.log (1 / (c * parameterNormOne h)) =
      Real.log (1 / parameterNormOne h) - Real.log c := by
    rw [Real.log_div one_ne_zero (mul_ne_zero hc.ne' hd.ne'),
      Real.log_div one_ne_zero hd.ne', Real.log_mul hc.ne' hd.ne', Real.log_one]
    ring
  rw [hlog] at he
  let E := savingPhi (((a : ℝ) / c, (b : ℝ) / c) + h) -
    savingPhi ((a : ℝ) / c, (b : ℝ) / c) - M.variation h * Real.log (1 / parameterNormOne h)
  have he' : |c * E + c * M.variation h * Real.log c| ≤ C * (c * parameterNormOne h) := by
    convert he using 1
    congr 1
    dsimp [E]
    ring
  have hcorr : |c * M.variation h * Real.log c| ≤
      c * (M.bound * parameterNormOne h) * |Real.log c| := by
    rw [abs_mul, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (M.variation_bound h hmem) hc.le) (abs_nonneg _)
  have ht := abs_sub (c * E + c * M.variation h * Real.log c)
    (c * M.variation h * Real.log c)
  rw [add_sub_cancel_right, abs_mul, abs_of_pos hc] at ht
  change |E| ≤ _
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c * |E| ≤ C * (c * parameterNormOne h) + c * (M.bound * parameterNormOne h) * |Real.log c| :=
      ht.trans (add_le_add he' hcorr)
    _ = _ := by ring

theorem phi_directional_log_variation {a b c : ℤ} (M : SavingRadialModel a b c)
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) (hc : 0 < (c : ℝ))
    (hq : (a : ℝ) + 2 * b - c ≠ 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ v ∈ M.domain, parameterNormOne v = 1 →
      ∀ e : ℝ, 0 < e → e ≤ r →
      |savingPhi (((a : ℝ) / c, (b : ℝ) / c) + e • v) -
        savingPhi ((a : ℝ) / c, (b : ℝ) / c) -
        e * M.variation v * Real.log (1 / e)| ≤ C * e := by
  obtain ⟨r, C, hr, hC, hmodel⟩ := M.phi_log_variation ha hb hc hq
  refine ⟨r, C, hr, hC, ?_⟩
  intro v hmem hv e he her
  have hn : parameterNormOne (e • v) = e := by
    rw [parameterNormOne_smul, hv, mul_one, abs_of_pos he]
  simpa only [hn, M.variation_smul v hmem e he.le] using
    hmodel (e • v) (M.scale_mem v hmem e he.le) (by rwa [hn]) (by rwa [hn])

end SavingRadialModel

end PiIrrationality
