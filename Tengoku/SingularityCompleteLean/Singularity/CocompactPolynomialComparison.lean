import Tengoku.SingularityCompleteLean.Singularity.CocompactGreenBall
import Tengoku.SingularityCompleteLean.Singularity.CocompactRelativeDetour

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A global Green product comparison with polynomial loss

Choose the avoided ball radius logarithmically in endpoint distance. The
absolute double-exponential detour bound is then at most half the full Green
kernel, using the independently proved coarse exponential lower bound.
The entrance comparison loses only a polynomial factor in endpoint distance.
This is weaker than an Ancona inequality with a distance-independent constant.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A logarithmic radius makes a double-exponential bound smaller than half
of a specified exponential lower bound, uniformly in nonnegative distance.
@isnad1 id=ex.4h4v.s7.8a6b315c80a7 from=translated src=- shape=307b96ec vocab=09534f10
-/
theorem exists_log_radius_absorption (a b A c : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hA : 0 < A) (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ d ≥ 0,
      A * Real.exp (-c * Real.exp (Real.log (M * (1 + d)))) ≤
        (a / 2) * Real.exp (-b * d) := by
  let q := Real.log (2 * A / a)
  let M := (b + |q| + 1) / c
  have hM : 0 < M := div_pos (by positivity) hc
  have hcm : c * M = b + |q| + 1 := by dsimp [M]; field_simp
  have hq : q ≤ c * M := by rw [hcm]; linarith [le_abs_self q]
  have hbc : b ≤ c * M := by rw [hcm]; linarith [abs_nonneg q]
  have heA : (a / 2) * Real.exp q = A := by
    dsimp [q]
    rw [Real.exp_log (div_pos (mul_pos (by norm_num) hA) ha)]
    field_simp
  refine ⟨M, hM, ?_⟩
  intro d hd
  rw [Real.exp_log (mul_pos hM (by linarith))]
  have he : q + -c * (M * (1 + d)) ≤ -b * d := by
    have hm := mul_le_mul_of_nonneg_right hbc hd
    nlinarith
  calc
    _ = ((a / 2) * Real.exp q) * Real.exp (-c * (M * (1 + d))) := by rw [heA]
    _ = (a / 2) * Real.exp (q + -c * (M * (1 + d))) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

end Singularity
