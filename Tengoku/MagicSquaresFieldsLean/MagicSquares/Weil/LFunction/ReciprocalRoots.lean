import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.SplitPolynomial
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open Polynomial
open scoped BigOperators

/-- A complex polynomial with constant coefficient one factors into
`1 - alpha*T`, with exactly its degree many factors. The `alpha` values
are the reciprocals of its roots.-/
theorem exists_reciprocal_roots (P : Polynomial ℂ) (hP : P.coeff 0 = 1) :
    ∃ (d : ℕ) (alpha : Fin d → ℂ), d = P.natDegree ∧
      P = ∏ i, (1 - C (alpha i) * X) := by
  classical
  have hP0 : P ≠ 0 := by intro hz; simp [hz] at hP
  have hzero : P.eval 0 = 1 := by rw [← Polynomial.coeff_zero_eq_eval_zero, hP]
  let l := P.roots.toList
  let a : Fin l.length → ℂ := l.get
  have hdegree : l.length = P.natDegree := by
    simpa [l] using (IsAlgClosed.card_roots_eq_natDegree (p := P))
  have hmem (i : Fin l.length) : a i ∈ P.roots := by
    exact Multiset.mem_toList.mp (List.get_mem l i)
  have hne (i : Fin l.length) : a i ≠ 0 := by
    intro hz
    have he := (Polynomial.mem_roots hP0).mp (hmem i)
    rw [Polynomial.IsRoot, hz, hzero] at he
    exact one_ne_zero he
  have hprod : (∏ i, (X - C (a i))) = (P.roots.map (fun x => X - C x)).prod := by
    rw [show (∏ i, (X - C (a i))) = (l.map (fun x => X - C x)).prod from
      Fin.prod_univ_fun_getElem l (fun x => X - C x)]
    change (Multiset.map (fun x => X - C x) (l : Multiset ℂ)).prod = _
    rw [show (l : Multiset ℂ) = P.roots from Multiset.coe_toList _]
  have hfactor : P = C P.leadingCoeff * ∏ i, (X - C (a i)) := by
    rw [hprod]
    exact (IsAlgClosed.splits P).eq_prod_roots
  have hconst : P.leadingCoeff * ∏ i, -a i = 1 := by
    have h := congrArg (Polynomial.eval (0 : ℂ)) hfactor
    simpa only [hzero, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, zero_sub] using h.symm
  refine ⟨l.length, fun i => (a i)⁻¹, hdegree, ?_⟩
  calc
    P = C P.leadingCoeff * ∏ i, (C (-a i) * (1 - C ((a i)⁻¹) * X)) := by
      conv_lhs => rw [hfactor]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, neg_mul, mul_inv_cancel₀ (hne i)]
      simp [sub_eq_add_neg, add_comm]
    _ = C (P.leadingCoeff * ∏ i, -a i) * ∏ i, (1 - C ((a i)⁻¹) * X) := by
      rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]
    _ = _ := by rw [hconst]; simp

variable {F : Type*} [Field F] [Fintype F]

/-- The finite L-polynomial constructed from the actual monic character
sums has at most `r-1` reciprocal roots. No character-sum estimate is assumed.-/
theorem splitLPolynomial_exists_reciprocal_roots {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) :
    ∃ (d : ℕ) (alpha : Fin d → ℂ), d ≤ r - 1 ∧
      splitLPolynomial roots chars = ∏ i, (1 - C (alpha i) * X) := by
  obtain ⟨d, alpha, hd, hfactor⟩ := exists_reciprocal_roots
    (splitLPolynomial roots chars) (splitLPolynomial_coeff_zero roots hinj chars hchars)
  exact ⟨d, alpha, hd ▸ splitLPolynomial_natDegree_le roots hinj chars hchars, hfactor⟩

end MagicSquares.LN97
