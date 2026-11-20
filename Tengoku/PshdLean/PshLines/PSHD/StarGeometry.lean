import Tengoku.Seed.Analysis.InnerProductSpace.Basic
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Radial separation for high-value stars

The elementary metric estimate in `pshd-vibe`, Lemma 1.3.
-/

namespace PshLines.PSHD

/-- Separate radial and angular contributions to squared distance.-/
theorem norm_smul_sub_sq_of_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (r s : ℝ) :
    ‖r • e - s • f‖ ^ 2 = (r - s) ^ 2 + r * s * ‖e - f‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he, hf,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- On a positive annulus the angular term has a uniform coefficient.-/
theorem annulus_chord_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    {R r s : ℝ} (hR : 0 ≤ R) (hr : R / 2 ≤ r) (hs : R / 2 ≤ s) :
    (r - s) ^ 2 + (R ^ 2 / 4) * ‖e - f‖ ^ 2 ≤ ‖r • e - s • f‖ ^ 2 := by
  rw [norm_smul_sub_sq_of_unit he hf]
  have hprod : R ^ 2 / 4 ≤ r * s := by
    calc
      R ^ 2 / 4 = (R / 2) * (R / 2) := by ring
      _ ≤ r * s := mul_le_mul hr hs (by positivity) (by linarith)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hprod (sq_nonneg _))

/-- Forgetting the phase of a Hermitian inner product only decreases the
chordal lower bound.-/
theorem chord_sq_lower_bound_inner_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    2 - 2 * ‖inner ℂ e f‖ ≤ ‖e - f‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), he, hf]
  have h := Complex.re_le_norm (inner ℂ e f)
  change 2 - 2 * ‖inner ℂ e f‖ ≤ 1 ^ 2 - 2 * (inner ℂ e f).re + 1 ^ 2
  linarith

/-- The phase-independent annular separation estimate used before the
Fubini--Study distance comparison in the star energy proof.-/
theorem annulus_inner_norm_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    {R r s : ℝ} (hR : 0 ≤ R) (hr : R / 2 ≤ r) (hs : R / 2 ≤ s) :
    (r - s) ^ 2 + (R ^ 2 / 4) * (2 - 2 * ‖inner ℂ e f‖) ≤
      ‖(r : ℂ) • e - (s : ℂ) • f‖ ^ 2 := by
  have hchord := chord_sq_lower_bound_inner_norm he hf
  let := InnerProductSpace.rclikeToReal ℂ E
  calc
    _ ≤ (r - s) ^ 2 + (R ^ 2 / 4) * ‖e - f‖ ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hchord (by positivity))
    _ ≤ _ := annulus_chord_lower_bound he hf hR hr hs

/-- Arbitrary phase choices satisfy the same annular separation estimate.
This applies directly to the measurable high-value circle selector.-/
theorem annulus_complex_smul_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    {R : ℝ} (hR : 0 ≤ R) {z w : ℂ}
    (hz : R / 2 ≤ ‖z‖) (hw : R / 2 ≤ ‖w‖) :
    (‖z‖ - ‖w‖) ^ 2 + (R ^ 2 / 4) * (2 - 2 * ‖inner ℂ e f‖) ≤
      ‖z • e - w • f‖ ^ 2 := by
  have hip : ‖inner ℂ e f‖ ≤ 1 := by
    simpa [he, hf] using norm_inner_le_norm e f
  have hprod : R ^ 2 / 4 ≤ ‖z‖ * ‖w‖ := by
    calc
      R ^ 2 / 4 = (R / 2) * (R / 2) := by ring
      _ ≤ ‖z‖ * ‖w‖ := mul_le_mul hz hw (by positivity) (norm_nonneg _)
  have hre := Complex.re_le_norm (inner ℂ (z • e) (w • f))
  have hnorm : ‖inner ℂ (z • e) (w • f)‖ =
      ‖z‖ * ‖w‖ * ‖inner ℂ e f‖ := by
    simp [inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm]
  rw [hnorm] at hre
  rw [norm_sub_sq (𝕜 := ℂ), norm_smul, norm_smul, he, hf]
  have hmul := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 2 - 2 * ‖inner ℂ e f‖ by
    linarith)
  change _ ≤ (‖z‖ * 1) ^ 2 - 2 * (inner ℂ (z • e) (w • f)).re + (‖w‖ * 1) ^ 2
  nlinarith

end PshLines.PSHD
