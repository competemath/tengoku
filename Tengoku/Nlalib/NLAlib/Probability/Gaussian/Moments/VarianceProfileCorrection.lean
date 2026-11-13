import Tengoku.Nlalib.NLAlib.Matrix.Functions.SpectralAbsoluteFactor
import Tengoku.Nlalib.NLAlib.Probability.SubGaussian.SortedMaximum
import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Basic.StandardVector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maximal Gaussian covariance corrections

Independent standard Gaussian coordinates realize the spectral
absolute-value correction with its exact row variance. The logarithmic
sub-Gaussian maximal inequality therefore applies directly, without an
assumed Gaussian covariance law.

Source: van Handel, arXiv:1502.05003v4, Theorem 4.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace NLAlib

/-- A finite linear form of independent standard Gaussian coordinates is
sub-Gaussian with its exact coefficient-square variance proxy.
@isnad1 id=hassubga.0h2v.s6.7ef2bbff8429 from=translated src=- shape=800bde5f vocab=ea444df5
-/
theorem hasSubgaussianMGF_sum_mul_gaussianVector {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasSubgaussianMGF (fun g : ι → ℝ => ∑ i, a i * g i)
      ⟨∑ i, a i ^ 2, Finset.sum_nonneg fun _i _ => sq_nonneg _⟩ (gaussianVector ι) := by
  have h := hasSubgaussianMGF_finset_sum_mul_of_iIndepFun
    (iIndepFun_eval_gaussianVector ι) (s := Finset.univ)
      (fun i _ => hasSubgaussianMGF_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector i)) a
  have hc : (∑ i, Real.toNNReal (a i ^ 2) * 1) =
      (⟨∑ i, a i ^ 2, Finset.sum_nonneg fun i _ => sq_nonneg _⟩ : ℝ≥0) := by
    apply Subtype.ext
    simp [sq_nonneg]
  rw [hc] at h
  exact h

/-- The actual Gaussian spectral correction has expected maximum at most
sixteen times any logarithmic envelope of its computed row variances.
@isnad1 id=le.3h3v.s8.8286b2590e9a from=translated src=- shape=f9a1c847 vocab=6807ac50
-/
theorem integral_norm_spectralAbsoluteFactor_mul_gaussianVector_le
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian)
    (D : ℝ) (hD : 0 < D)
    (henv : ∀ i, Real.sqrt (∑ j, B i j ^ 2) * Real.log (((i : ℕ) : ℝ) + 2) ≤ D ^ 2) :
    (∫ g, ‖fun i => ∑ k, spectralAbsoluteFactor hB i k * g k‖
      ∂gaussianVector (Fin n)) ≤ 16 * D := by
  apply integral_norm_pi_le_sixteen_of_hasSubgaussianMGF_log_envelope
    (μ := gaussianVector (Fin n))
    (fun i (g : Fin n → ℝ) => ∑ k, spectralAbsoluteFactor hB i k * g k)
      (fun i => ⟨∑ k, spectralAbsoluteFactor hB i k ^ 2,
        Finset.sum_nonneg fun k _ => sq_nonneg _⟩)
        (fun i => hasSubgaussianMGF_sum_mul_gaussianVector _) D hD
  intro i
  exact (mul_le_mul_of_nonneg_right (sum_sq_spectralAbsoluteFactor_row_le hB i)
    (Real.log_nonneg (by have hi : 0 ≤ (((i : ℕ) : ℝ)) := Nat.cast_nonneg _; linarith))).trans (henv i)

end NLAlib
