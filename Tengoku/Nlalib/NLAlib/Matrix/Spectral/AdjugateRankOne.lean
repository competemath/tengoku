import Tengoku.Seed.LinearAlgebra.Matrix.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The nonzero rank-one adjugate at nullity one

Rank normal form proves that nullity one gives a nonzero cofactor. The two
adjugate identities then force every column and row into the corresponding
one-dimensional kernels.
Source: Horn–Johnson (2013), Theorem 1.4.12.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

omit [DecidableEq n] in
/-- Transposition preserves the nullity of a square matrix over any field.
Source: Horn–Johnson (2013), §0.4; row rank equals column rank.-/
theorem finrank_ker_mulVecLin_transpose_eq (M : Matrix n n K) :
    finrank K (LinearMap.ker Mᵀ.mulVecLin) = finrank K (LinearMap.ker M.mulVecLin) := by
  have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hT := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
  change M.rank + _ = _ at hM
  change Mᵀ.rank + _ = _ at hT
  rw [Matrix.rank_transpose] at hT
  omega

/-- A square matrix of nullity one has a nonzero adjugate, including size
one where the cofactor is the empty determinant. Source: Horn–Johnson
(2013), Theorem 1.4.12; rank normal form gives a nonzero cofactor.-/
theorem adjugate_ne_zero_of_finrank_ker_eq_one (M : Matrix n n K)
    (hdim : finrank K (LinearMap.ker M.mulVecLin) = 1) : M.adjugate ≠ 0 := by
  classical
  have hr := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + finrank K (LinearMap.ker M.mulVecLin) = finrank K (n → K) at hr
  rw [hdim, Module.finrank_fintype_fun_eq_card] at hr
  have hnull : Fintype.card n - M.rank = 1 := by omega
  obtain ⟨V, U, e, hV, hU, hM⟩ := Matrix.exists_rank_normal_form M
  let j : Fin M.rank ⊕ Fin (Fintype.card n - M.rank) := Sum.inr ⟨0, by omega⟩
  let d : Fin M.rank ⊕ Fin (Fintype.card n - M.rank) → K := Sum.elim (fun _ => 1) (fun _ => 0)
  have hblock : (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) K) 0 0
      (0 : Matrix (Fin (Fintype.card n - M.rank)) (Fin (Fintype.card n - M.rank)) K)) =
      Matrix.diagonal d := by
    simpa only [Matrix.diagonal_one, Matrix.diagonal_zero] using
      Matrix.fromBlocks_diagonal (fun _ : Fin M.rank => (1 : K))
        (fun _ : Fin (Fintype.card n - M.rank) => (0 : K))
  have hdiag : (Matrix.diagonal d).adjugate j j = 1 := by
    rw [Matrix.adjugate_diagonal, Matrix.diagonal_apply_eq]
    apply Finset.prod_eq_one
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    cases k with
    | inl k => rfl
    | inr k =>
      exfalso
      apply hkj
      congr 1
      apply Fin.ext
      have := k.isLt
      dsimp [j]
      omega
  intro hzero
  have hadj : (V * M * U).adjugate = 0 := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hzero,
      Matrix.zero_mul, Matrix.mul_zero]
  rw [hM, hblock, Matrix.adjugate_submatrix_equiv_self] at hadj
  have hj := congrArg (fun N => N (e.symm j) (e.symm j)) hadj
  have hj' : (Matrix.diagonal d).adjugate j j = 0 := by simpa using hj
  exact one_ne_zero (hdiag.symm.trans hj')

end NLAlib
