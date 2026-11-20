/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimplexCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem centered_integer_norm_identity (z : ι → ℤ) (a : ℤ) (hsum : (∑ i, z i) = a) :
    (∑ i, ((z i : ℚ)-(a : ℚ)/Fintype.card ι)^2) =
      (a : ℚ)*(Fintype.card ι-a)/Fintype.card ι +
        ∑ i, (z i : ℚ)*((z i : ℚ)-1) := by
  have hn : (Fintype.card ι : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ i, (z i : ℚ)) = (a : ℚ) := by exact_mod_cast hsum
  have hpoint (t : ℚ) : (t-(a : ℚ)/Fintype.card ι)^2 =
      t*(t-1)+(1-2*(a : ℚ)/Fintype.card ι)*t+((a : ℚ)/Fintype.card ι)^2 := by ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem integer_mul_pred_nonneg (z : ℤ) : 0 ≤ (z : ℚ)*((z : ℚ)-1) := by
  have h : z ≤ 0 ∨ 1 ≤ z := by omega
  rcases h with h | h
  · have hQ : (z : ℚ) ≤ 0 := by exact_mod_cast h
    exact mul_nonneg_of_nonpos_of_nonpos hQ (by linarith)
  · have hQ : (1 : ℚ) ≤ z := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)

theorem centered_integer_norm_minimum (z : ι → ℤ) (a : ℤ) (hsum : (∑ i, z i) = a) :
    (a : ℚ)*(Fintype.card ι-a)/Fintype.card ι ≤
      ∑ i, ((z i : ℚ)-(a : ℚ)/Fintype.card ι)^2 := by
  rw [centered_integer_norm_identity z a hsum]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => integer_mul_pred_nonneg (z i)))

theorem centered_integer_norm_eq_iff (z : ι → ℤ) (a : ℤ) (hsum : (∑ i, z i) = a) :
    (∑ i, ((z i : ℚ)-(a : ℚ)/Fintype.card ι)^2) =
      (a : ℚ)*(Fintype.card ι-a)/Fintype.card ι ↔ ∀ i, z i = 0 ∨ z i = 1 := by
  rw [centered_integer_norm_identity z a hsum, add_eq_left]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => integer_mul_pred_nonneg (z i))]
  simp only [Finset.mem_univ, forall_const]
  constructor
  · intro h i
    rcases mul_eq_zero.mp (h i) with h0 | h1
    · exact Or.inl (by exact_mod_cast h0)
    · have hQ : (z i : ℚ) = 1 := by linarith
      exact Or.inr (by exact_mod_cast hQ)
  · intro h i
    rcases h i with h | h <;> simp [h]

end SRG266.Lattice
