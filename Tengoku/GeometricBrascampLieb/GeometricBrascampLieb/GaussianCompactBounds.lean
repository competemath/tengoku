import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gaussian bounds uniform over compact sets of centers

These are the spatial tail estimates needed when the initial data have bounded
support. The bounds apply to every polynomial degree, so they cover derivatives
of all orders of the Gaussian kernel.
-/

noncomputable section
open MeasureTheory

namespace GeometricBrascampLieb

theorem pow_mul_gaussian_le (r : ℝ) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    r ^ n * Real.exp (-b * r ^ 2) ≤
      (1 + (n.factorial : ℝ) / (b / 2) ^ n) * Real.exp (-(b / 2) * r ^ 2) := by
  have hp : r ^ n ≤ 1 + (r ^ 2) ^ n := by
    rw [← pow_mul, mul_comm 2 n, pow_mul]
    nlinarith [sq_nonneg (r ^ n - 1)]
  have he : Real.exp (-b * r ^ 2) ≤ Real.exp (-(b / 2) * r ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg r]
  calc
    _ ≤ (1 + (r ^ 2) ^ n) * Real.exp (-b * r ^ 2) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-b * r ^ 2) + (r ^ 2) ^ n * Real.exp (-b * r ^ 2) := by ring
    _ ≤ Real.exp (-(b / 2) * r ^ 2) +
        ((n.factorial : ℝ) / (b / 2) ^ n) * Real.exp (-(b / 2) * r ^ 2) :=
      add_le_add he (even_pow_mul_gaussian_le r n hb)
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E]

theorem half_norm_sq_sub_norm_sq_le (x z : E) :
    ‖x‖ ^ 2 / 2 - ‖z‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  have hn : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - z) z
  have hs : ‖x‖ ^ 2 ≤ (‖x - z‖ + ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg x) hn 2
  nlinarith [sq_nonneg (‖x - z‖ - ‖z‖)]

theorem gaussian_shift_le_uniform (x z : E) {R b : ℝ} (hR : ‖z‖ ≤ R) (hb : 0 ≤ b) :
    Real.exp (-b * ‖x - z‖ ^ 2) ≤
      Real.exp (b * R ^ 2) * Real.exp (-(b / 2) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hz : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hR 2
  have h := mul_le_mul_of_nonneg_left (half_norm_sq_sub_norm_sq_le x z) hb
  nlinarith [mul_le_mul_of_nonneg_left hz hb]

theorem norm_sub_pow_mul_gaussian_le_uniform (x z : E) (n : ℕ) {R b : ℝ}
    (hR : ‖z‖ ≤ R) (hb : 0 < b) :
    ‖x - z‖ ^ n * Real.exp (-b * ‖x - z‖ ^ 2) ≤
      ((1 + (n.factorial : ℝ) / (b / 2) ^ n) * Real.exp ((b / 2) * R ^ 2)) *
        Real.exp (-(b / 4) * ‖x‖ ^ 2) := by
  calc
    _ ≤ (1 + (n.factorial : ℝ) / (b / 2) ^ n) * Real.exp (-(b / 2) * ‖x - z‖ ^ 2) :=
      pow_mul_gaussian_le _ n hb
    _ ≤ (1 + (n.factorial : ℝ) / (b / 2) ^ n) *
        (Real.exp ((b / 2) * R ^ 2) * Real.exp (-((b / 2) / 2) * ‖x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (gaussian_shift_le_uniform x z hR (half_pos hb).le) (by positivity)
    _ = _ := by rw [mul_assoc]; congr 3; ring

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- One integrable function controls all centers in a fixed ball.-/
theorem exists_integrable_gaussian_majorant (R : ℝ) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ g : E → ℝ, Integrable g ∧ ∀ x z, ‖z‖ ≤ R →
      ‖x - z‖ ^ n * Real.exp (-b * ‖x - z‖ ^ 2) ≤ g x := by
  refine ⟨fun x => ((1 + (n.factorial : ℝ) / (b / 2) ^ n) * Real.exp ((b / 2) * R ^ 2)) *
    Real.exp (-(b / 4) * ‖x‖ ^ 2), ?_, ?_⟩
  · exact (integrable_gaussian (E := E) (by positivity : 0 < b / 4)).const_mul _
  · exact fun x z hz => norm_sub_pow_mul_gaussian_le_uniform x z n hz hb

end GeometricBrascampLieb
