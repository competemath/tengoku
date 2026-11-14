import Tengoku.Piirrationalitymeasure.Formalization.BinetLaplace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A symmetric Laplace integral connects the two forms of Binet's formula. -/

namespace PiIrrationality

open MeasureTheory Set

noncomputable def binetPairKernel (y a u : ℝ) : ℝ :=
  Real.exp (-(y * u)) * (2 * u / (u ^ 2 + a ^ 2))

/--
@isnad1 id=le.1h3v.s4.02402d9f227b from=translated src=- shape=3666ff6c vocab=f07252d4
-/
theorem binetPairKernel_nonneg {y a u : ℝ} (hu : 0 ≤ u) : 0 ≤ binetPairKernel y a u := by
  unfold binetPairKernel
  positivity

/--
@isnad1 id=le.2h3v.s6.4583ba828eb2 from=translated src=- shape=b24d69cd vocab=01d447ca
-/
theorem binetPairKernel_bound {y a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    binetPairKernel y a u ≤ (2 / a ^ 2) * (u * Real.exp (-(y * u))) := by
  have hden : 0 < u ^ 2 + a ^ 2 := by positivity
  have h := div_le_div_of_nonneg_left (show 0 ≤ 2 * u by positivity)
    (sq_pos_of_pos ha) (show a ^ 2 ≤ u ^ 2 + a ^ 2 by nlinarith [sq_nonneg u])
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(y * u))).le
  convert! hm using 1 <;> ring

/--
@isnad1 id=integrab.2h2v.s6.fbba5a72ce94 from=translated src=- shape=004a5d89 vocab=d1f6053e
-/
theorem integrableOn_binetPairKernel {y a : ℝ} (hy : 0 < y) (ha : 0 < a) :
    IntegrableOn (binetPairKernel y a) (Ioi 0) := by
  have hi := (integrableOn_pow_mul_exp_neg_mul hy 1).const_mul (2 / a ^ 2)
  apply hi.mono' (by unfold binetPairKernel; fun_prop)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [Real.norm_of_nonneg (binetPairKernel_nonneg hu.le)]
  simpa only [pow_one] using binetPairKernel_bound ha hu.le

/--
@isnad1 id=le.2h2v.s7.ef41ae678368 from=translated src=- shape=3fc1677a vocab=7951ea7e
-/
theorem integral_binetPairKernel_bound {y a : ℝ} (hy : 0 < y) (ha : 0 < a) :
    (∫ u : ℝ in Ioi 0, binetPairKernel y a u) ≤ 2 / a ^ 2 / y ^ 2 := by
  have hi := (integrableOn_pow_mul_exp_neg_mul hy 1).const_mul (2 / a ^ 2)
  have hb : (∫ u : ℝ in Ioi 0, binetPairKernel y a u) ≤
      ∫ u : ℝ in Ioi 0, (2 / a ^ 2) * (u ^ 1 * Real.exp (-(y * u))) := by
    apply integral_mono_ae (integrableOn_binetPairKernel hy ha) hi
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    simpa only [pow_one] using binetPairKernel_bound ha hu.le
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul hy 1] at hb
  simpa only [Nat.factorial_one, Nat.cast_one, Nat.reduceAdd, mul_one_div] using hb

/--
@isnad1 id=eq.2h2v.s6.73be7a122e0a from=translated src=- shape=a06376e1 vocab=94280fc4
-/
theorem integral_binetPairKernel_symm {y a : ℝ} (hy : 0 < y) (ha : 0 < a) :
    (∫ u : ℝ in Ioi 0, binetPairKernel y a u) =
      ∫ u : ℝ in Ioi 0, binetPairKernel a y u := by
  have hchange := integral_comp_mul_left_Ioi' (binetPairKernel y a) 0 (div_pos ha hy)
  rw [mul_zero, smul_eq_mul, ← integral_const_mul] at hchange
  rw [← hchange]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  unfold binetPairKernel
  have hexp : -(y * (a / y * u)) = -(a * u) := by field_simp
  rw [hexp]
  field_simp
  <;> ring

end PiIrrationality
