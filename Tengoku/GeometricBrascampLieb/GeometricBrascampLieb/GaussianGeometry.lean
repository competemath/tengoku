import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianFlow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Completing the square for geometric Gaussian products

The common heat scale is preserved by geometric BL data; arbitrary centers
contribute exactly the nonnegative quadratic defect.
-/

noncomputable section
open scoped BigOperators

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)] (D : Datum ι E F)

theorem synthesis_sub (v w : ∀ i, F i) :
    D.synthesis (fun i => v i - w i) = D.synthesis v - D.synthesis w := by
  simp only [synthesis, map_sub, smul_sub, Finset.sum_sub_distrib]

theorem synthesis_smul (c : ℝ) (v : ∀ i, F i) :
    D.synthesis (fun i => c • v i) = c • D.synthesis v := by
  simp only [synthesis, map_smul, Finset.smul_sum, smul_smul, mul_comm]

/-- The constant left after completing the square.-/
def gaussianDefect (z : ∀ i, F i) : ℝ :=
  (∑ i, D.weight i * ‖z i‖ ^ 2) - ‖D.synthesis z‖ ^ 2

theorem gaussianDefect_nonneg (z : ∀ i, F i) : 0 ≤ D.gaussianDefect z := D.defect_nonneg z

theorem sum_weight_norm_sub_sq (z : ∀ i, F i) (x : E) :
    ∑ i, D.weight i * ‖D.map i x - z i‖ ^ 2 =
      ‖x - D.synthesis z‖ ^ 2 + D.gaussianDefect z := by
  have hcross : (∑ i, D.weight i * (2 * inner ℝ (D.map i x) (z i))) =
      2 * inner ℝ x (D.synthesis z) := by
    calc
      _ = 2 * ∑ i, D.weight i * inner ℝ (z i) (D.map i x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (D.map i x)]
        ring
      _ = _ := by rw [← D.synthesis_inner, real_inner_comm (D.synthesis z)]
  simp only [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, D.sum_weight_norm_sq, hcross, gaussianDefect]
  ring

variable [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]

theorem gaussian_logProduct (a : ι → ℝ) (z : ∀ i, F i) (t : ℝ) (x : E) :
    D.logProduct (fun i => gaussianLogHeatFlow (a i) (z i)) t x =
      gaussianLog (∑ i, D.weight i * a i) (D.synthesis z) t x -
        (4 * t)⁻¹ * D.gaussianDefect z := by
  have hdim : (∑ i, D.weight i * ((Module.finrank ℝ (F i) : ℝ) / 2 * Real.log t)) =
      (Module.finrank ℝ E : ℝ) / 2 * Real.log t := by
    calc
      _ = (∑ i, D.weight i * (Module.finrank ℝ (F i) : ℝ)) * (Real.log t / 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [D.dimension_identity]; ring
  have hquad : (∑ i, D.weight i * ((4 * t)⁻¹ * ‖D.map i x - z i‖ ^ 2)) =
      (4 * t)⁻¹ * ∑ i, D.weight i * ‖D.map i x - z i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [logProduct, gaussianLogHeatFlow, gaussianLog, mul_sub, Finset.sum_sub_distrib]
  rw [hdim, hquad, D.sum_weight_norm_sub_sq]
  ring

theorem gaussian_heatProduct (a : ι → ℝ) (z : ∀ i, F i) (t : ℝ) (x : E) :
    D.heatProduct (fun i => gaussianLogHeatFlow (a i) (z i)) t x =
      Real.exp ((∑ i, D.weight i * a i) - (Module.finrank ℝ E : ℝ) / 2 * Real.log t -
        (4 * t)⁻¹ * D.gaussianDefect z) * Real.exp (-(4 * t)⁻¹ * ‖x - D.synthesis z‖ ^ 2) := by
  rw [heatProduct, D.gaussian_logProduct, gaussianLog, ← Real.exp_add]
  congr 1
  ring

omit [FiniteDimensional ℝ E] in
theorem gaussian_score (a : ι → ℝ) (z : ∀ i, F i) (t : ℝ) (x : E) :
    D.score (fun i => gaussianLogHeatFlow (a i) (z i)) t x =
      -(2 * t)⁻¹ • (x - D.synthesis z) := by
  simp only [score, gaussianLogHeatFlow, gaussianScore, D.synthesis_smul, D.synthesis_sub]
  rw [show D.synthesis (fun i => D.map i x) = x from D.resolution_apply x]

theorem gaussian_timeRate (a : ι → ℝ) (z : ∀ i, F i) (t : ℝ) (x : E) :
    D.timeRate (fun i => gaussianLogHeatFlow (a i) (z i)) t x =
      -(2 * t)⁻¹ * (Module.finrank ℝ E : ℝ) + (2 * t)⁻¹ ^ 2 *
        (‖x - D.synthesis z‖ ^ 2 + D.gaussianDefect z) := by
  simp only [timeRate, gaussianLogHeatFlow, gaussianHessian, gaussianScore,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_id,
    map_smul, LinearMap.trace_id, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, neg_sq, mul_add, Finset.sum_add_distrib]
  have hs (f : ι → ℝ) (c : ℝ) : (∑ i, D.weight i * (c * f i)) =
      c * ∑ i, D.weight i * f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, hs, D.dimension_identity, D.sum_weight_norm_sub_sq]
  ring

omit [FiniteDimensional ℝ E] in
theorem gaussian_scoreDerivative (a : ι → ℝ) (z : ∀ i, F i) (t : ℝ) (x : E) :
    D.scoreDerivative (fun i => gaussianLogHeatFlow (a i) (z i)) t x =
      -(2 * t)⁻¹ • ContinuousLinearMap.id ℝ E := by
  simp only [scoreDerivative, gaussianLogHeatFlow, gaussianHessian,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_smul,
    smul_smul]
  simp_rw [mul_comm (D.weight _) (-(2 * t)⁻¹), ← smul_smul]
  rw [← Finset.smul_sum, D.resolution]

end GeometricBrascampLieb.Datum
