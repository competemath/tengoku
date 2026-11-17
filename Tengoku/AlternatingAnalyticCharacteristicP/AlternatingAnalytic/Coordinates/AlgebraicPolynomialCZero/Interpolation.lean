import Tengoku.Seed.LinearAlgebra.Vandermonde
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.LinearAlgebra.Multilinear.Basic
import Tengoku.Seed.Algebra.BigOperators.GroupWithZero.Finset
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inverse-Vandermonde interpolation of algebraic homogeneous polynomials

Let `b` be an `n`-linear map (not assumed continuous) and `v : ι → E` finitely many vectors.
Evaluating the diagonal `y ↦ b (y, …, y)` at the grid points `∑ j, ν (g j) • v j`, where
`g : ι → Fin (n + 1)` selects distinct nodes `ν`, and weighting with entries of the inverse
Vandermonde matrix in each coordinate isolates the sum of `b (v ∘ f)` over the words `f` with a
prescribed multiplicity function. This is the interpolation step in the proof of Proposition I.2.
-/

open Finset

namespace AlgebraicPolynomialCZero

variable {K E Z : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup Z] [Module K Z]

/-- The inverse Vandermonde matrix of distinct nodes inverts evaluation of monomials.
@isnad1 id=eq.1h5v.s8.bc63490e7d41 from=translated src=- shape=8d8bec58 vocab=17d4a301
-/
theorem inv_vandermonde_mul_pow {n : ℕ} (ν : Fin (n + 1) → K) (hν : Function.Injective ν)
    (i c : Fin (n + 1)) :
    ∑ k, (Matrix.vandermonde ν)⁻¹ i k * ν k ^ (c : ℕ) = if i = c then 1 else 0 := by
  have hdet : IsUnit (Matrix.vandermonde ν).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hν)
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul _ hdet) i) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa [Matrix.vandermonde_apply] using h

/-- The number of positions of a word `f` taking the value `j`, as an element of `Fin (n + 1)`.-/
def wordCount {ι : Type*} [DecidableEq ι] {n : ℕ} (f : Fin n → ι) (j : ι) : Fin (n + 1) :=
  ⟨#{r | f r = j}, Nat.lt_succ_of_le ((card_filter_le _ _).trans (by simp))⟩

/--
@isnad1 id=eq.0h4v.s6.ed50cb5fe1a5 from=translated src=- shape=0edb4ed9 vocab=b4942afa
-/
theorem wordCount_val {ι : Type*} [DecidableEq ι] {n : ℕ} (f : Fin n → ι) (j : ι) :
    (wordCount f j : ℕ) = #{r | f r = j} := rfl

/-- The product of node values along a word is a product of powers over the letters.
@isnad1 id=eq.0h5v.s6.197941b8fde9 from=translated src=- shape=3626e639 vocab=03ad86ad
-/
theorem prod_word_eq_prod_pow {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (w : ι → K) (f : Fin n → ι) :
    ∏ r, w (f r) = ∏ j, w j ^ (wordCount f j : ℕ) := by
  rw [← Finset.prod_fiberwise Finset.univ f (fun r => w (f r))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun r hr => by rw [(Finset.mem_filter.mp hr).2]),
    Finset.prod_const, wordCount_val]

/-- Inverse-Vandermonde weights on the grid isolate the words with a
prescribed multiplicity function `m`.
@isnad1 id=eq.1h9v.s9.aff0d1fcc31b from=translated src=- shape=b768dc11 vocab=50724d21
-/
theorem sum_interpolation {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (ν : Fin (n + 1) → K) (hν : Function.Injective ν)
    (b : MultilinearMap K (fun _ : Fin n => E) Z) (v : ι → E) (m : ι → Fin (n + 1)) :
    ∑ g : ι → Fin (n + 1), (∏ j, (Matrix.vandermonde ν)⁻¹ (m j) (g j)) •
        b (fun _ => ∑ j, ν (g j) • v j) =
      ∑ f ∈ univ.filter (fun f : Fin n → ι => ∀ j, wordCount f j = m j), b (fun r => v (f r)) := by
  set M := (Matrix.vandermonde ν)⁻¹
  have hexp : ∀ g : ι → Fin (n + 1), b (fun _ => ∑ j, ν (g j) • v j) =
      ∑ f : Fin n → ι, (∏ r, ν (g (f r))) • b (fun r => v (f r)) := by
    intro g
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact MultilinearMap.map_smul_univ b (fun r => ν (g (f r))) (fun r => v (f r))
  have hscalar : ∀ f : Fin n → ι,
      ∑ g : ι → Fin (n + 1), (∏ j, M (m j) (g j)) * ∏ r, ν (g (f r)) =
        if ∀ j, wordCount f j = m j then 1 else 0 := by
    intro f
    calc ∑ g : ι → Fin (n + 1), (∏ j, M (m j) (g j)) * ∏ r, ν (g (f r))
        = ∑ g : ι → Fin (n + 1), ∏ j, (M (m j) (g j) * ν (g j) ^ (wordCount f j : ℕ)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [prod_word_eq_prod_pow (fun j => ν (g j)) f, Finset.prod_mul_distrib]
      _ = ∏ j, ∑ k, M (m j) k * ν k ^ (wordCount f j : ℕ) := by
          rw [Fintype.prod_sum]
      _ = ∏ j, (if wordCount f j = m j then (1 : K) else 0) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [inv_vandermonde_mul_pow ν hν]
          exact if_congr eq_comm rfl rfl
      _ = _ := Fintype.prod_boole
  calc ∑ g : ι → Fin (n + 1), (∏ j, M (m j) (g j)) • b (fun _ => ∑ j, ν (g j) • v j)
      = ∑ g : ι → Fin (n + 1), ∑ f : Fin n → ι,
          ((∏ j, M (m j) (g j)) * ∏ r, ν (g (f r))) • b (fun r => v (f r)) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hexp, Finset.smul_sum]
        simp only [smul_smul]
    _ = ∑ f : Fin n → ι, (∑ g : ι → Fin (n + 1), (∏ j, M (m j) (g j)) * ∏ r, ν (g (f r))) •
          b (fun r => v (f r)) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_smul]
    _ = ∑ f : Fin n → ι, (if ∀ j, wordCount f j = m j then (1 : K) else 0) •
          b (fun r => v (f r)) := by
        simp only [hscalar]
    _ = _ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun f _ => ?_
        split_ifs <;> simp

end AlgebraicPolynomialCZero
