import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.HeatRegularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Geometric maps transport quadratic growth bounds -/

noncomputable section
open scoped BigOperators

namespace GeometricBrascampLieb.Datum

theorem norm_add_sq_le (a r : ℝ) : ‖a+r^2‖ ≤ ‖a‖+r^2 := by
  calc
    _ ≤ ‖a‖+‖r^2‖ := norm_add_le _ _
    _ = _ := by rw [Real.norm_eq_abs (r^2), abs_of_nonneg (sq_nonneg r)]

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)] (D : Datum ι E F)

theorem norm_adjoint_apply (i : ι) (v : F i) : ‖(D.map i).adjoint v‖ = ‖v‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (D.adjoint_norm_sq i v)

theorem norm_map_apply_le (i : ι) (x : E) : ‖D.map i x‖ ≤ ‖x‖ := by
  have h := real_inner_le_norm x ((D.map i).adjoint (D.map i x))
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq, D.norm_adjoint_apply] at h
  by_cases hz : ‖D.map i x‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hp : 0 < ‖D.map i x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using h) hp

theorem norm_lift_le (i : ι) (H : F i →L[ℝ] F i) :
    ‖(D.map i).adjoint.comp (H.comp (D.map i))‖ ≤ ‖H‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H)
  intro x
  simp only [ContinuousLinearMap.comp_apply, D.norm_adjoint_apply]
  exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_left (D.norm_map_apply_le i x) (norm_nonneg H))

variable [∀ i, FiniteDimensional ℝ (F i)]

def growthCoefficient (a : ι → ℝ) : ℝ :=
  ∑ i, D.weight i * (1+‖operatorTrace (E := F i)‖) * a i

theorem growthCoefficient_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    0 ≤ D.growthCoefficient a := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (D.weight_nonneg i) (by positivity)) (ha i)

theorem weighted_growth_le {a v : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (r : ℝ)
    (hv : ∀ i, v i ≤ a i*(1+r^2)) :
    ∑ i, D.weight i*v i ≤ D.growthCoefficient a*(1+r^2) := by
  rw [growthCoefficient, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ D.weight i * (a i*(1+r^2)) := mul_le_mul_of_nonneg_left (hv i) (D.weight_nonneg i)
    _ ≤ D.weight i * ((1+‖operatorTrace (E := F i)‖)*a i*(1+r^2)) := by
      apply mul_le_mul_of_nonneg_left _ (D.weight_nonneg i)
      nlinarith [mul_nonneg (norm_nonneg (operatorTrace (E := F i)))
        (mul_nonneg (ha i) (show 0 ≤ 1+r^2 by positivity))]
    _ = _ := by ring

variable (U : ∀ i, LogHeatFlow (F i))

theorem score_sq_le_of_growth (t : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hg : ∀ i y, ‖(U i).gradient t y‖^2 ≤ a i*(1+‖y‖^2)) (x : E) :
    ‖D.score U t x‖^2 ≤ D.growthCoefficient a*(1+‖x‖^2) := by
  apply (D.synthesis_norm_sq_le _).trans (D.weighted_growth_le ha ‖x‖ _)
  intro i
  apply (hg i (D.map i x)).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (pow_le_pow_left₀ (norm_nonneg _) (D.norm_map_apply_le i x) 2)) (ha i)

theorem scoreDerivative_le_of_growth (t : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hH : ∀ i y, ‖(U i).hessian t y‖ ≤ a i*(1+‖y‖^2)) (x : E) :
    ‖D.scoreDerivative U t x‖ ≤ D.growthCoefficient a*(1+‖x‖^2) := by
  apply (norm_sum_le _ _).trans
  have hl : ∑ i, ‖D.weight i • (D.map i).adjoint.comp (((U i).hessian t (D.map i x)).comp (D.map i))‖ ≤
      ∑ i, D.weight i*‖(U i).hessian t (D.map i x)‖ := by
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (D.weight_nonneg i)]
    exact mul_le_mul_of_nonneg_left (D.norm_lift_le i _) (D.weight_nonneg i)
  apply hl.trans (D.weighted_growth_le ha ‖x‖ _)
  intro i
  apply (hH i (D.map i x)).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (pow_le_pow_left₀ (norm_nonneg _) (D.norm_map_apply_le i x) 2)) (ha i)

theorem timeRate_le_of_growth (t : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hg : ∀ i y, ‖(U i).gradient t y‖^2 ≤ a i*(1+‖y‖^2))
    (hH : ∀ i y, ‖(U i).hessian t y‖ ≤ a i*(1+‖y‖^2)) (x : E) :
    ‖D.timeRate U t x‖ ≤ D.growthCoefficient a*(1+‖x‖^2) := by
  apply (norm_sum_le _ _).trans
  rw [growthCoefficient, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, Real.norm_eq_abs (D.weight i), abs_of_nonneg (D.weight_nonneg i)]
  have hm : a i*(1+‖D.map i x‖^2) ≤ a i*(1+‖x‖^2) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (pow_le_pow_left₀ (norm_nonneg _) (D.norm_map_apply_le i x) 2)) (ha i)
  have hgrad := (hg i (D.map i x)).trans hm
  have hhess := (hH i (D.map i x)).trans hm
  calc
    _ ≤ D.weight i*(‖LinearMap.trace ℝ (F i) ((U i).hessian t (D.map i x)).toLinearMap‖ +
        ‖(U i).gradient t (D.map i x)‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (D.weight_nonneg i)
      exact norm_add_sq_le _ _
    _ ≤ D.weight i*(‖operatorTrace (E := F i)‖*(a i*(1+‖x‖^2)) + a i*(1+‖x‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (D.weight_nonneg i)
      exact add_le_add ((norm_trace_le _).trans (mul_le_mul_of_nonneg_left hhess
        (norm_nonneg (operatorTrace (E := F i))))) hgrad
    _ = _ := by ring

end GeometricBrascampLieb.Datum
