import Tengoku.Piirrationalitymeasure.Formalization.BinetLaplace
import Tengoku.Seed.Analysis.SpecialFunctions.FrullaniIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The recurrence of the Laplace expression in Binet's formula. -/

namespace PiIrrationality

open MeasureTheory Set Filter
open scoped Topology

private theorem exp_neg_mul_succ (y u : ℝ) :
    Real.exp (-((y + 1) * u)) = Real.exp (-(y * u)) * Real.exp (-u) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem exp_sub_div_bounds (y : ℝ) {u : ℝ} (hu : 0 < u) :
    0 ≤ (Real.exp (-(y * u)) - Real.exp (-((y + 1) * u))) / u ∧
      (Real.exp (-(y * u)) - Real.exp (-((y + 1) * u))) / u ≤ Real.exp (-(y * u)) := by
  have h0 : 0 ≤ 1 - Real.exp (-u) := by
    have h := Real.exp_le_one_iff.mpr (by linarith : -u ≤ 0)
    linarith
  have h1 : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
  rw [exp_neg_mul_succ]
  constructor
  · apply div_nonneg _ hu.le
    nlinarith [mul_nonneg (Real.exp_pos (-(y * u))).le h0]
  · rw [div_le_iff₀ hu]
    nlinarith [mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(y * u))).le]

theorem integrableOn_exp_sub_div {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u => (Real.exp (-(y * u)) - Real.exp (-((y + 1) * u))) / u) (Ioi 0) := by
  have hi : IntegrableOn (fun u => Real.exp (-(y * u))) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_pow_mul_exp_neg_mul hy 0
  apply hi.mono'
  · have hm : Measurable (fun u => (Real.exp (-(y * u)) - Real.exp (-((y + 1) * u))) / u) := by
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (exp_sub_div_bounds y hu).1]
    exact (exp_sub_div_bounds y hu).2

theorem integral_exp_sub_div {y : ℝ} (hy : 0 < y) :
    (∫ u : ℝ in Ioi 0, (Real.exp (-(y * u)) - Real.exp (-((y + 1) * u))) / u) =
      Real.log ((y + 1) / y) := by
  have hc : Continuous (fun u : ℝ => Real.exp (-u)) := by fun_prop
  have h0 : Tendsto (fun u : ℝ => Real.exp (-u)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa only [neg_zero, Real.exp_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h := Frullani.integral_Ioi_eq (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    hy (by linarith : 0 < y + 1) h0 hinf (by
      simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using integrableOn_exp_sub_div hy)
  simpa only [smul_eq_mul, sub_zero, mul_one, one_mul, div_eq_mul_inv, mul_comm] using h

private theorem binetKernel_difference (y : ℝ) {u : ℝ} (hu : 0 < u) :
    Real.exp (-(y * u)) * binetKernel u - Real.exp (-((y + 1) * u)) * binetKernel u =
      (Real.exp (-(y * u)) + Real.exp (-((y + 1) * u))) / 2 -
        (Real.exp (-(y * u)) - Real.exp (-((y + 1) * u))) / u := by
  have he : Real.exp u - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)).ne'
  have he0 := (Real.exp_pos u).ne'
  simp only [exp_neg_mul_succ, Real.exp_neg u, binetKernel]
  generalize Real.exp u = e at he he0 ⊢
  field_simp [he, he0, hu.ne']
  ring

theorem binetLaplace_sub_succ {y : ℝ} (hy : 0 < y) :
    binetLaplace y - binetLaplace (y + 1) =
      (1 / y + 1 / (y + 1)) / 2 - Real.log ((y + 1) / y) := by
  have hy1 : 0 < y + 1 := by linarith
  have he (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun u => Real.exp (-(a * u))) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_pow_mul_exp_neg_mul ha 0
  have heval (a : ℝ) (ha : 0 < a) :
      (∫ u : ℝ in Ioi 0, Real.exp (-(a * u))) = 1 / a := by
    simpa only [pow_zero, one_mul, Nat.zero_add, pow_one, Nat.factorial_zero, Nat.cast_one] using
      integral_pow_mul_exp_neg_mul ha 0
  have hmean : IntegrableOn (fun u =>
      (Real.exp (-(y * u)) + Real.exp (-((y + 1) * u))) / 2) (Ioi 0) :=
    ((he y hy).add (he (y + 1) hy1)).div_const 2
  unfold binetLaplace
  rw [← integral_sub (integrableOn_binetLaplace hy) (integrableOn_binetLaplace hy1)]
  calc
    _ = ∫ u : ℝ in Ioi 0,
        (Real.exp (-(y * u)) + Real.exp (-((y + 1) * u))) / 2 -
          (Real.exp (-(y * u)) - Real.exp (-((y + 1) * u))) / u :=
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => binetKernel_difference y hu)
    _ = _ := by
      rw [integral_sub hmean (integrableOn_exp_sub_div hy), integral_div,
        integral_add (he y hy) (he (y + 1) hy1), heval y hy, heval (y + 1) hy1,
        integral_exp_sub_div hy]

noncomputable def binetDigamma (y : ℝ) : ℝ := Real.log y - 1 / (2 * y) - binetLaplace y

theorem binetDigamma_add_one {y : ℝ} (hy : 0 < y) :
    binetDigamma (y + 1) = binetDigamma y + 1 / y := by
  have h := binetLaplace_sub_succ hy
  rw [Real.log_div (by linarith) hy.ne'] at h
  unfold binetDigamma
  field_simp at h ⊢
  linarith

theorem binetDigamma_add_nat {y : ℝ} (hy : 0 < y) (N : ℕ) :
    binetDigamma (y + N) = binetDigamma y + ∑ q ∈ Finset.range N, 1 / (y + (q : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : 0 < y + (N : ℝ) := add_pos_of_pos_of_nonneg hy (Nat.cast_nonneg N)
    rw [Nat.cast_succ, ← add_assoc, binetDigamma_add_one hN, ih, Finset.sum_range_succ]
    ring

end PiIrrationality
