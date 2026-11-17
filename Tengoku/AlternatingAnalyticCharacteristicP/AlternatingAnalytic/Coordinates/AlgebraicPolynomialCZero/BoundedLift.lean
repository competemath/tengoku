import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.CZeroCoordinates
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Coordinates.AlgebraicPolynomialCZero.SortedWords
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Coordinates.AlgebraicPolynomialCZero.DiagonalNorm
import Tengoku.Seed.Analysis.Normed.Group.Ultra
import Tengoku.Seed.SetTheory.Ordinal.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded lifts of continuous algebraic polynomials on `c₀` (Proposition I.2)

Over a nonarchimedean field `K` (not necessarily complete), a continuous diagonal
`p x = b (x, …, x)` of an `n`-linear map `b : c₀(I, K)ⁿ → Z` (not assumed continuous), with `Z`
complete and nonarchimedean, has a bounded `n`-linear lift `q` with `‖q‖ ≤ L ^ n ‖p‖_diag`.
Here `L` bounds the inverse Vandermonde matrix of the nodes `1, t, …, tⁿ` for a fixed
`0 < |t| < 1`, so it depends only on `K` and `n`. The lift is built from the symmetrized
coefficients on sorted words, bounded by interpolation on the unit grid.
-/

open Finset Filter
open scoped ZeroAtInfty Topology

namespace AlgebraicPolynomialCZero

universe uK uI uZ

section Constants

variable (K : Type uK) [NontriviallyNormedField K]

/-- A fixed scalar of norm strictly between `0` and `1`.-/
noncomputable def node : K := Classical.choose (NormedField.exists_norm_lt_one K)

theorem norm_node_pos : 0 < ‖node K‖ := (Classical.choose_spec (NormedField.exists_norm_lt_one K)).1

theorem norm_node_lt_one : ‖node K‖ < 1 :=
  (Classical.choose_spec (NormedField.exists_norm_lt_one K)).2

/-- The interpolation nodes `1, t, …, tⁿ`.-/
noncomputable def nodes (n : ℕ) : Fin (n + 1) → K := fun k => node K ^ (k : ℕ)

theorem nodes_injective (n : ℕ) : Function.Injective (nodes K n) := by
  intro k l h
  have h' : ‖node K‖ ^ (k : ℕ) = ‖node K‖ ^ (l : ℕ) := by
    simpa [nodes, norm_pow] using congrArg norm h
  exact Fin.ext (pow_right_injective₀ (norm_node_pos K) (norm_node_lt_one K).ne h')

theorem norm_nodes_le_one (n : ℕ) (k : Fin (n + 1)) : ‖nodes K n k‖ ≤ 1 := by
  rw [nodes, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_node_lt_one K).le

/-- A bound `L ≥ 1` for the entries of the inverse Vandermonde matrix of the nodes.-/
noncomputable def lagrangeConst (n : ℕ) : ℝ :=
  1 + ∑ i, ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖

theorem one_le_lagrangeConst (n : ℕ) : 1 ≤ lagrangeConst K n :=
  le_add_of_nonneg_right (sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _)

theorem norm_inv_vandermonde_le (n : ℕ) (i k : Fin (n + 1)) :
    ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ ≤ lagrangeConst K n := by
  have hk : ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ ≤
      ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ :=
    single_le_sum (f := fun k => ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖)
      (fun _ _ => norm_nonneg _) (mem_univ k)
  have hi : ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ ≤
      ∑ i, ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ :=
    single_le_sum (f := fun i => ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖)
      (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ i)
  rw [lagrangeConst]
  linarith

/-- The lifting constant `L ^ n` of Proposition I.2.-/
noncomputable def liftConst (n : ℕ) : ℝ := lagrangeConst K n ^ n

theorem one_le_liftConst (n : ℕ) : 1 ≤ liftConst K n :=
  one_le_pow₀ (one_le_lagrangeConst K n)

end Constants

section Coefficients

variable {K : Type uK} [NontriviallyNormedField K] [IsUltrametricDist K]
  {I : Type uI} [TopologicalSpace I] [DiscreteTopology I]
  {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [IsUltrametricDist Z] {n : ℕ}

/-- A grid vector `∑ j, ν (g j) • e_j` with nodes in the unit ball has norm at most one.-/
theorem norm_gridVector_le {S : Finset I} (w : S → K) (hw : ∀ j, ‖w j‖ ≤ 1) :
    ‖∑ j, w j • CZero.coordinate (K := K) (j : I)‖ ≤ 1 := by
  refine (CZero.norm_le zero_le_one).mpr fun i => ?_
  have hi : (∑ j, w j • CZero.coordinate (K := K) (j : I)) i =
      ∑ j, w j * CZero.coordinate (K := K) (j : I) i := by
    rw [← CZero.evalCLM_apply, map_sum]
    simp
  rw [hi]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hw j)).trans
    ((CZero.norm_apply_le _ i).trans (CZero.norm_coordinate_le _))

variable [LinearOrder I]

end Coefficients

end AlgebraicPolynomialCZero
