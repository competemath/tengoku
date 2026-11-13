import Tengoku.Nlalib.NLAlib.Polynomial.FunctionApproximation.JacksonTensorApproximation
import Tengoku.Seed.Analysis.Real.Pi.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform bounds for normalized Chebyshev basis functions

The unnormalized Chebyshev measure has mass `π`, so every normalized basis
function has absolute value at most one on its approximation interval.
-/

noncomputable section
open Real Polynomial Finset
namespace NLAlib

/-- Normalized Chebyshev weights lie in the unit interval.
@isnad1 id=mem.0h1v.s4.2ea3040cbfcd from=translated src=- shape=39e72392 vocab=ed73a92a
-/
theorem normalizedChebyshevWeight_mem_Icc (j : ℕ) :
    normalizedChebyshevWeight j ∈ Set.Icc (0 : ℝ) 1 := by
  have hnon : 0 ≤ normalizedChebyshevWeight j := sqrt_nonneg _
  refine ⟨hnon,?_⟩
  have hs : normalizedChebyshevWeight j ^ 2 ≤ 1 := by
    rw [normalizedChebyshevWeight_sq]
    apply (div_le_one pi_pos).mpr
    split_ifs <;> linarith [pi_gt_three]
  nlinarith

/-- Every normalized basis function is bounded on the exact closed interval.
@isnad1 id=le.1h2v.s5.380383316ac8 from=translated src=- shape=8d2a4a41 vocab=5cef032e
-/
theorem abs_normalizedChebyshev_le_one (j : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |normalizedChebyshev j x| ≤ 1 := by
  rw [normalizedChebyshev,abs_mul,abs_of_nonneg (normalizedChebyshevWeight_mem_Icc j).1]
  exact (mul_le_mul (normalizedChebyshevWeight_mem_Icc j).2
    (Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx)) (abs_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by norm_num)

/-- The genuine normalized tensor basis is bounded on the approximation cube.
@isnad1 id=le.1h3v.s5.0094ff0e1b8c from=translated src=- shape=d4f82c77 vocab=92037083
-/
theorem abs_tensorNormalizedChebyshev_le_one {ι : Type*} [Fintype ι]
    (α : ι → ℕ) {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) :
    |tensorNormalizedChebyshev α x| ≤ 1 := by
  rw [tensorNormalizedChebyshev,Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => abs_normalizedChebyshev_le_one _ (hx i))

end NLAlib
