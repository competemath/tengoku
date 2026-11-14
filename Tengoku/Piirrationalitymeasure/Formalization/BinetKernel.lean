import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Tengoku.Seed.NumberTheory.ZetaValues

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The positive partial-fraction kernel for Binet's digamma formula. -/

namespace PiIrrationality

noncomputable def binetKernel (u : ℝ) : ℝ :=
  1 / (Real.exp u - 1) - 1 / u + 1 / 2

private theorem neg_mul_I_mem_integerComplement {t : ℝ} (ht : 0 < t) :
    -(t : ℂ) * Complex.I ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have h := congrArg Complex.im hn
  simp at h
  linarith

private theorem cotTerm_neg_mul_I_im (t : ℝ) (n : ℕ) :
    (cotTerm (-(t : ℂ) * Complex.I) n).im =
      2 * t / (t ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  simp [cotTerm, Complex.normSq_apply]
  ring

private theorem cot_neg_mul_I {t : ℝ} (ht : 0 < t) :
    Complex.cot ((Real.pi : ℂ) * (-(t : ℂ) * Complex.I)) =
      ((Real.exp (2 * Real.pi * t) + 1) / (Real.exp (2 * Real.pi * t) - 1) : ℝ) *
        Complex.I := by
  have he : Real.exp (2 * Real.pi * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  have heC : (Real.exp (2 * Real.pi * t) : ℂ) - 1 ≠ 0 := by exact_mod_cast he
  have ha : 2 * (Real.pi : ℂ) * Complex.I * (-(t : ℂ) * Complex.I) =
      ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [Complex.cot_pi_eq_exp_ratio, ha, ← Complex.ofReal_exp]
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]
  rw [show (1 : ℂ) - Real.exp (2 * Real.pi * t) =
    -((Real.exp (2 * Real.pi * t) : ℂ) - 1) by ring]
  field_simp [heC]
  simp only [Complex.I_sq]
  ring

private theorem cot_main_neg_mul_I_im {t : ℝ} (ht : 0 < t) :
    ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (-(t : ℂ) * Complex.I)) -
      1 / (-(t : ℂ) * Complex.I)).im = 2 * Real.pi * binetKernel (2 * Real.pi * t) := by
  rw [cot_neg_mul_I ht]
  have he : Real.exp (2 * Real.pi * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add,
    Complex.div_im, Complex.one_im, Complex.one_re, Complex.neg_im, Complex.neg_re,
    Complex.normSq_apply, neg_zero, sub_zero, neg_mul]
  unfold binetKernel
  generalize Real.exp (2 * Real.pi * t) = e at he ⊢
  field_simp [ht.ne', Real.pi_ne_zero, he]
  ring

/--
@isnad1 id=hassum.1h1v.s7.50e6603512e5 from=translated src=- shape=d3a3ec64 vocab=f4a7a4fb
-/
theorem hasSum_binetKernel_scaled {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => t / (Real.pi * (t ^ 2 + ((n : ℝ) + 1) ^ 2)))
      (binetKernel (2 * Real.pi * t)) := by
  have hx := neg_mul_I_mem_integerComplement ht
  have hs : HasSum (cotTerm (-(t : ℂ) * Complex.I))
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (-(t : ℂ) * Complex.I)) -
        1 / (-(t : ℂ) * Complex.I)) := by
    rw [cot_series_rep' hx]
    exact (summable_cotTerm hx).hasSum
  have him := (Complex.hasSum_im hs).div_const (2 * Real.pi)
  simp_rw [cotTerm_neg_mul_I_im, cot_main_neg_mul_I_im ht] at him
  convert! him using 1
  · funext n
    field_simp
  · field_simp

/--
@isnad1 id=hassum.1h1v.s7.2aff5389cdf6 from=translated src=- shape=ccebde43 vocab=f4a7a4fb
-/
theorem hasSum_binetKernel {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => 2 * u / (u ^ 2 + (2 * Real.pi * ((n : ℝ) + 1)) ^ 2))
      (binetKernel u) := by
  have hs := hasSum_binetKernel_scaled (div_pos hu (by positivity : 0 < 2 * Real.pi))
  rw [mul_div_cancel₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)] at hs
  convert! hs using 1
  funext n
  field_simp

/--
@isnad1 id=lt.1h1v.s4.77e1a9f71e6b from=translated src=- shape=35bd48ee vocab=92c183f4
-/
theorem binetKernel_pos {u : ℝ} (hu : 0 < u) : 0 < binetKernel u := by
  have hs := hasSum_binetKernel hu
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos (fun n => by positivity) 0 (by positivity)

end PiIrrationality
