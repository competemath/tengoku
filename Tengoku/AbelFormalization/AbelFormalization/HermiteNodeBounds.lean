import Tengoku.Seed.Algebra.Polynomial.BigOperators
import Tengoku.Seed.Algebra.Order.BigOperators.GroupWithZero.Finset
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Hermite node polynomials and contour denominators

The node polynomial uses multiplicities without a distinct-node hypothesis.
Coincident nodes combine by addition of their multiplicities, and a fixed
distance between the nodes and the contour bounds its denominator away from zero.
-/

noncomputable section

open Polynomial

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

/-- The node polynomial for Hermite interpolation.-/
def nodePolynomial (δ : ι → ℂ) (m : ι → ℕ) : ℂ[X] :=
  ∏ i, (X - C (δ i)) ^ m i

def totalMultiplicity (m : ι → ℕ) : ℕ := ∑ i, m i

theorem nodePolynomial_monic (δ : ι → ℂ) (m : ι → ℕ) :
    (nodePolynomial δ m).Monic := by
  apply monic_prod_of_monic
  intro i _
  exact (monic_X_sub_C (δ i)).pow (m i)

theorem nodePolynomial_ne_zero (δ : ι → ℂ) (m : ι → ℕ) :
    nodePolynomial δ m ≠ 0 := (nodePolynomial_monic δ m).ne_zero

theorem nodePolynomial_natDegree (δ : ι → ℂ) (m : ι → ℕ) :
    (nodePolynomial δ m).natDegree = totalMultiplicity m := by
  unfold nodePolynomial totalMultiplicity
  rw [natDegree_prod_of_monic Finset.univ (fun i => (X - C (δ i)) ^ m i)
    (fun i _ => (monic_X_sub_C (δ i)).pow (m i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [(monic_X_sub_C (δ i)).natDegree_pow, natDegree_X_sub_C, mul_one]

theorem nodePolynomial_degree (δ : ι → ℂ) (m : ι → ℕ) :
    (nodePolynomial δ m).degree = (totalMultiplicity m : WithBot ℕ) := by
  rw [degree_eq_natDegree (nodePolynomial_ne_zero δ m), nodePolynomial_natDegree]

theorem nodePolynomial_eval (δ : ι → ℂ) (m : ι → ℕ) (ζ : ℂ) :
    (nodePolynomial δ m).eval ζ = ∏ i, (ζ - δ i) ^ m i := by
  unfold nodePolynomial
  rw [Polynomial.eval_prod]
  simp only [eval_pow, eval_sub, eval_X, eval_C]

theorem norm_nodePolynomial_eval (δ : ι → ℂ) (m : ι → ℕ) (ζ : ℂ) :
    ‖(nodePolynomial δ m).eval ζ‖ = ∏ i, ‖ζ - δ i‖ ^ m i := by
  rw [nodePolynomial_eval, norm_prod]
  simp only [norm_pow]

def nodeMultiplicity (δ : ι → ℂ) (m : ι → ℕ) (ξ : ℂ) : ℕ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => δ i = ξ), m i

def nodePolynomialAway (δ : ι → ℂ) (m : ι → ℕ) (ξ : ℂ) : ℂ[X] := by
  classical
  exact ∏ i ∈ Finset.univ.filter (fun i => δ i ≠ ξ), (X - C (δ i)) ^ m i

/-- Equal nodes combine into a single factor with the sum of their multiplicities.-/
theorem nodePolynomial_group_at (δ : ι → ℂ) (m : ι → ℕ) (ξ : ℂ) :
    nodePolynomial δ m =
      (X - C ξ) ^ nodeMultiplicity δ m ξ * nodePolynomialAway δ m ξ := by
  classical
  have he : (∏ i ∈ Finset.univ.filter (fun i => δ i = ξ), (X - C (δ i)) ^ m i) =
      (X - C ξ) ^ nodeMultiplicity δ m ξ := by
    calc
      (∏ i ∈ Finset.univ.filter (fun i => δ i = ξ), (X - C (δ i)) ^ m i)
          = ∏ i ∈ Finset.univ.filter (fun i => δ i = ξ), (X - C ξ) ^ m i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  have hs := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => δ i = ξ) (fun i => (X - C (δ i)) ^ m i)
  rw [he] at hs
  exact hs.symm

theorem grouped_node_factor_dvd (δ : ι → ℂ) (m : ι → ℕ) (ξ : ℂ) :
    (X - C ξ) ^ nodeMultiplicity δ m ξ ∣ nodePolynomial δ m := by
  rw [nodePolynomial_group_at]
  exact dvd_mul_right _ _

end AbelFormalization
