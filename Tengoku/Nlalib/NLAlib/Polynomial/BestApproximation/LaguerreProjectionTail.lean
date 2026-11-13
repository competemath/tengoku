import Tengoku.Nlalib.NLAlib.Polynomial.BestApproximation.LaguerreProjection
import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.LaguerreRecurrence
import Tengoku.Nlalib.NLAlib.ForMathlib.Algebra.Polynomial.PositiveTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic positivity of the finite Laguerre projection on its tail

The shifted monic recurrence gives a finite coefficient certificate. This proves
the signs of every derivative directly and replaces root-location arguments.
Source: focused reciprocal reroute, positivity beyond the cutoff `4n`.
-/

noncomputable section
open Polynomial
open scoped Nat
namespace NLAlib

/-- Each weighted Laguerre term is a positive multiple of the monic polynomial.
Source: focused reciprocal reroute, positive tail factors.
@isnad1 id=eq.0h1v.s7.500c9d921c4c from=translated src=- shape=4603b7b6 vocab=ab8d96dd
-/
theorem laguerreExponentialCoefficient_smul_eq_monic (j : ℕ) :
    laguerreExponentialCoefficient j • laguerrePolynomial j =
      (4 / ((3:ℝ)^(j+1) * (j ! :ℝ))) • monicLaguerrePolynomial j := by
  rw [monicLaguerrePolynomial, smul_smul]
  congr 1
  dsimp [laguerreExponentialCoefficient]
  field_simp

/-- Every coefficient of the shifted projection is nonnegative, with positive
constant coefficient and, in positive degree, positive linear coefficient.
This is an exact finite certificate for the actual Laguerre projection.
Source: focused reciprocal reroute, the tail positivity step.
atlas: exp-rational-halfline (partial)
@isnad1 id=and.0h1v.s8.a8ba7091509a from=translated src=- shape=97d46651 vocab=17903903
-/
theorem shifted_laguerreExponentialProjection_coeff_certificate (n : ℕ) :
    (∀ k, 0 ≤ ((laguerreExponentialProjection n).comp (X+C (4*(n:ℝ)))).coeff k) ∧
    0 < ((laguerreExponentialProjection n).comp (X+C (4*(n:ℝ)))).coeff 0 ∧
    (0 < n → 0 < ((laguerreExponentialProjection n).comp (X+C (4*(n:ℝ)))).coeff 1) := by
  have hP (j : Fin (n+1)) := shifted_laguerre_recurrence_coeff_certificate
    monicLaguerrePolynomial monicLaguerrePolynomial_zero monicLaguerrePolynomial_succ_eq
    n j.val (by omega)
  have hterm (j : Fin (n+1)) (k : ℕ) :
      0 ≤ ((laguerreExponentialCoefficient j.val • laguerrePolynomial j.val).comp
        (X+C (4*(n:ℝ)))).coeff k := by
    rw [laguerreExponentialCoefficient_smul_eq_monic, smul_comp, coeff_smul,
      smul_eq_mul]
    exact mul_nonneg (by positivity) ((hP j).1 k)
  have hterm0 (j : Fin (n+1)) :
      0 < ((laguerreExponentialCoefficient j.val • laguerrePolynomial j.val).comp
        (X+C (4*(n:ℝ)))).coeff 0 := by
    rw [laguerreExponentialCoefficient_smul_eq_monic, smul_comp, coeff_smul,
      smul_eq_mul]
    exact mul_pos (by positivity) (hP j).2.2.1
  have heq (k : ℕ) : ((laguerreExponentialProjection n).comp
      (X+C (4*(n:ℝ)))).coeff k = ∑ j : Fin (n+1),
        ((laguerreExponentialCoefficient j.val • laguerrePolynomial j.val).comp
          (X+C (4*(n:ℝ)))).coeff k := by
    simp only [laguerreExponentialProjection, sum_comp, finsetSum_coeff]
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rw [heq]
    exact Finset.sum_nonneg (fun j _ => hterm j k)
  · rw [heq]
    exact (hterm0 0).trans_le (Finset.single_le_sum (fun j _ => hterm j 0)
      (Finset.mem_univ 0))
  · intro hn
    let j : Fin (n+1) := ⟨1, by omega⟩
    have hterm1 :
        0 < ((laguerreExponentialCoefficient j.val • laguerrePolynomial j.val).comp
          (X+C (4*(n:ℝ)))).coeff 1 := by
      rw [laguerreExponentialCoefficient_smul_eq_monic, smul_comp, coeff_smul,
        smul_eq_mul]
      exact mul_pos (by positivity) ((hP j).2.2.2 (by norm_num [j]))
    rw [heq]
    exact hterm1.trans_le (Finset.single_le_sum (fun j _ => hterm j 1)
      (Finset.mem_univ j))

/-- Every derivative of the actual finite Laguerre projection is nonnegative
throughout its tail. No splitting-field or eigenvalue premise is needed.
Source: focused reciprocal reroute, positive tail.
atlas: exp-rational-halfline (partial)
@isnad1 id=le.1h3v.s7.7d6b695622ce from=translated src=- shape=e27eefae vocab=088fed54
-/
theorem iterate_derivative_laguerreExponentialProjection_eval_nonneg
    (n r : ℕ) {x : ℝ} (hx : 4*(n:ℝ) ≤ x) :
    0 ≤ ((derivative : ℝ[X] → ℝ[X])^[r] (laguerreExponentialProjection n)).eval x :=
  iterate_derivative_eval_nonneg_of_shifted_coeff_nonneg
    (shifted_laguerreExponentialProjection_coeff_certificate n).1 hx r

/-- The finite Laguerre projection itself is strictly positive on the tail.
Source: focused reciprocal reroute, positive tail.
atlas: exp-rational-halfline (partial)
@isnad1 id=lt.1h2v.s5.089c16c29ba0 from=translated src=- shape=1e5ec29e vocab=07c72480
-/
theorem laguerreExponentialProjection_eval_pos (n : ℕ)
    {x : ℝ} (hx : 4*(n:ℝ) ≤ x) :
    0 < (laguerreExponentialProjection n).eval x :=
  eval_pos_of_shifted_coeff_nonneg
    (shifted_laguerreExponentialProjection_coeff_certificate n).1
    (shifted_laguerreExponentialProjection_coeff_certificate n).2.1 hx

/-- Its first derivative is strictly positive in every positive degree.
Source: focused reciprocal reroute, positive tail.
atlas: exp-rational-halfline (partial)
@isnad1 id=lt.2h2v.s7.6dc627123a5c from=translated src=- shape=e275fe5d vocab=4103ae4f
-/
theorem laguerreExponentialProjection_derivative_eval_pos {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 4*(n:ℝ) ≤ x) :
    0 < (laguerreExponentialProjection n).derivative.eval x :=
  derivative_eval_pos_of_shifted_coeff_nonneg
    (shifted_laguerreExponentialProjection_coeff_certificate n).1
    ((shifted_laguerreExponentialProjection_coeff_certificate n).2.2 hn) hx

end NLAlib
