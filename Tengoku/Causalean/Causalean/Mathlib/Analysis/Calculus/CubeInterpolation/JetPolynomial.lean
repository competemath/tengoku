module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Directional
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Grid
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.JetHomogeneous
public import Tengoku

/-!
# Polynomial realization of a finite Taylor jet

The diagonal evaluations of finitely many multilinear derivatives form a
multivariate polynomial. At a smooth point its coordinate derivatives recover
the corresponding coordinate derivatives of the original function.
-/

public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The order-`m` Taylor expression at a point is the evaluation of a
multivariate polynomial with degree at most `m` in each coordinate. -/
theorem taylor_expression_polynomial (d m : ℕ)
    (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ∃ p : MvPolynomial (Fin d) ℝ,
      (∀ i, p.degreeOf i ≤ m) ∧
      ∀ y : Fin d → ℝ,
        MvPolynomial.eval y p =
          ∑ k ∈ Finset.range (m + 1),
            (Nat.factorial k : ℝ)⁻¹ *
              iteratedFDeriv ℝ k u x (fun _ => y - x) := by
  classical
  let q : ℕ → MvPolynomial (Fin d) ℝ := fun k =>
    ∑ f : Fin k → Fin d,
      MvPolynomial.C ((Nat.factorial k : ℝ)⁻¹ * coordPartial k u f x) *
        ∏ a : Fin k, (MvPolynomial.X (f a) - MvPolynomial.C (x (f a)))
  have hfactor :
      ∀ a : Fin d, (MvPolynomial.X a - MvPolynomial.C (x a)).totalDegree ≤ 1 := by
    intro a
    have h := MvPolynomial.totalDegree_add
      (MvPolynomial.X a : MvPolynomial (Fin d) ℝ) (-MvPolynomial.C (x a))
    simpa only [sub_eq_add_neg] using le_trans h (by simp :
      max (MvPolynomial.X a : MvPolynomial (Fin d) ℝ).totalDegree
        (-MvPolynomial.C (x a)).totalDegree ≤ 1)
  have hq (k : ℕ) : (q k).totalDegree ≤ k := by
    unfold q
    apply le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun f _ => ?_)
    apply le_trans (MvPolynomial.totalDegree_mul _ _) 
    have hc : (MvPolynomial.C ((Nat.factorial k : ℝ)⁻¹ * coordPartial k u f x) :
        MvPolynomial (Fin d) ℝ).totalDegree = 0 := MvPolynomial.totalDegree_C _
    rw [hc, zero_add]
    apply le_trans (MvPolynomial.totalDegree_finsetProd _ _)
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun a _ => hfactor (f a)))
  refine ⟨∑ k ∈ Finset.range (m + 1), q k, ?_, ?_⟩
  · intro i
    apply le_trans (MvPolynomial.degreeOf_le_totalDegree _ _)
    apply le_trans (MvPolynomial.totalDegree_finsetSum _ _)
    apply Finset.sup_le
    intro k hk
    exact (hq k).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  · intro y
    simp only [MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [q, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_prod,
      MvPolynomial.eval_sub, MvPolynomial.eval_X]
    rw [diagonal_derivative_coordinate_expansion u x (y - x)]
    simp_rw [Pi.sub_apply]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    ring

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
