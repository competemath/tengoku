import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.ProjectedRamps

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE

namespace SubpolynomialLp

lemma interval_moment_error (a M b α T : ℝ) (hb : 0 ≤ b) (hα : 1 ≤ α)
    (hT : 0 ≤ T) (hlo : a ≤ M) (hhi : M ≤ α*a+T) :
    |M-b| ≤ α*|a-b|+(α-1)*b+T := by
  have ha := abs_le.mp (le_refl |a-b|)
  have he : 0 ≤ (α-1)*|a-b| := mul_nonneg (by linarith) (abs_nonneg _)
  have he' : 0 ≤ (α-1)*b := mul_nonneg (by linarith) hb
  apply abs_le.mpr
  constructor <;> nlinarith

lemma weighted_variance_power {E : Type uE} [Fintype E] (w a : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (ha : ∀ e, 0 ≤ a e) (r B T : ℝ)
    (hr : 1 < r) (hB0 : 0 ≤ B) (hB : ∀ e, a e ≤ B) (hT : ∑ e, w e*a e ≤ T) :
    (∑ e, w e*(a e)^r) ≤ B^(r-1)*T := by
  have he (e : E) : (a e)^r ≤ B^(r-1)*a e := by
    calc
      _ = (a e)^(r-1)*a e := by rw [← Real.rpow_add_one' (ha e) (by linarith : r-1+1 ≠ 0)]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (ha e) (hB e) (by linarith)) (ha e)
  calc
    _ ≤ ∑ e, w e*(B^(r-1)*a e) := Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (he e) (hw e))
    _ = B^(r-1)*(∑ e, w e*a e) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg hB0 _)

lemma variance_power_algebra (p H U : ℝ) (hH : 0 < H) (hU : 0 < U) :
    (H^2*U)^(p/2-1)*(4*U) = (4*U^(p/2))*H^(p-2) := by
  rw [Real.mul_rpow (sq_nonneg H) hU.le]
  have hHpow : (H^2)^(p/2-1)=H^(p-2) := by
    rw [← Real.rpow_natCast_mul hH.le]
    congr 1
    norm_num
    ring
  have hUpow : U^(p/2-1)*U=U^(p/2) := by
    rw [← Real.rpow_add_one hU.ne']
    congr 1
    ring
  rw [hHpow]
  calc
    _ = 4*(U^(p/2-1)*U)*H^(p-2) := by ring
    _ = _ := by rw [hUpow]

end SubpolynomialLp

end

end OAI
