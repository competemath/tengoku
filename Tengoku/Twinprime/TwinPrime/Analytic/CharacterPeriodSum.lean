import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing
import Tengoku.Seed.Data.Nat.Periodic
import Tengoku.Seed.Algebra.BigOperators.Intervals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complete-period cancellation for nonprincipal characters

The complete sum is zero for every nonprincipal character, without a
primitivity assumption. Exact periodicity reduces an initial sum to its
remainder modulo the positive modulus. The principal character is excluded
only from cancellation statements, not from the elementary length bound.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

theorem character_sum_range_modulus_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  calc
    _ = ∑ z : ZMod q, χ z := by
      apply sum_bij (fun (n : ℕ) _ => (n : ZMod q))
      · intro n _
        exact mem_univ _
      · intro a ha b hb hab
        have hv := congrArg ZMod.val hab
        simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
          ZMod.val_natCast_of_lt (mem_range.mp hb)] using hv
      · intro z _
        exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
      · intro n _
        rfl
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

private theorem sum_Ioc_zero_eq_shifted_range (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, f n = ∑ n ∈ range N, f (n + 1) := by
  have hI : Ioc 0 N = Ico 1 (N + 1) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hI, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

theorem character_sum_shifted_range_modulus_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ ((n + 1 : ℕ) : ZMod q) = 0 := by
  have hs := sum_range_succ' (fun n : ℕ => χ (n : ZMod q)) q
  rw [sum_range_succ, character_sum_range_modulus_eq_zero χ hχ] at hs
  simpa only [Nat.cast_zero, ZMod.natCast_self, zero_add, add_eq_right] using hs.symm

/-- The initial sum is exactly its remainder sum; no estimate is used.-/
theorem character_sum_Ioc_eq_mod {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, χ (n : ZMod q) =
      ∑ n ∈ Ioc 0 (N % q), χ (n : ZMod q) := by
  have hp : Function.Periodic
      (fun K : ℕ => ∑ n ∈ range K, χ ((n + 1 : ℕ) : ZMod q)) q := by
    intro K
    dsimp only
    rw [Nat.add_comm K q, sum_range_add, character_sum_shifted_range_modulus_eq_zero χ hχ]
    simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
  simpa only [sum_Ioc_zero_eq_shifted_range] using (hp.map_mod_nat N).symm

/-- The elementary length bound includes principal characters and modulus zero.-/
theorem norm_character_sum_Ioc_le_length {q : ℕ}
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, χ (n : ZMod q)‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ Ioc 0 N, (1 : ℝ) := sum_le_sum fun n _ => χ.norm_le_one _
    _ = _ := by simp

theorem norm_character_sum_Ioc_le_remainder {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, χ (n : ZMod q)‖ ≤ (N % q : ℕ) := by
  rw [character_sum_Ioc_eq_mod χ hχ]
  exact norm_character_sum_Ioc_le_length χ (N % q)

/-- A bound for all nonprincipal characters, including imprimitive ones.-/
theorem norm_character_sum_Ioc_le_modulus {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, χ (n : ZMod q)‖ ≤ (q : ℝ) :=
  (norm_character_sum_Ioc_le_remainder χ hχ N).trans
    (by exact_mod_cast (Nat.mod_lt N (NeZero.pos q)).le)

theorem norm_character_sum_Ioc_interval_le_length {q : ℕ}
    (χ : DirichletCharacter ℂ q) (M N : ℕ) :
    ‖∑ n ∈ Ioc M N, χ (n : ZMod q)‖ ≤ (N - M : ℕ) := by
  calc
    _ ≤ ∑ n ∈ Ioc M N, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ Ioc M N, (1 : ℝ) := sum_le_sum fun n _ => χ.norm_le_one _
    _ = _ := by simp

/-- A general interval is the difference of two bounded initial sums.
The statement includes empty intervals and both endpoints zero.-/
theorem norm_character_sum_Ioc_interval_le_two_modulus {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Ioc M N, χ (n : ZMod q)‖ ≤ 2 * (q : ℝ) := by
  by_cases hMN : M ≤ N
  · have heq : (∑ n ∈ Ioc M N, χ (n : ZMod q)) =
        (∑ n ∈ Ioc 0 N, χ (n : ZMod q)) - ∑ n ∈ Ioc 0 M, χ (n : ZMod q) := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using
        sum_Ioc_consecutive (fun n : ℕ => χ (n : ZMod q)) (Nat.zero_le M) hMN
    rw [heq]
    calc
      _ ≤ ‖∑ n ∈ Ioc 0 N, χ (n : ZMod q)‖ + ‖∑ n ∈ Ioc 0 M, χ (n : ZMod q)‖ := norm_sub_le _ _
      _ ≤ (q : ℝ) + q := add_le_add (norm_character_sum_Ioc_le_modulus χ hχ N)
        (norm_character_sum_Ioc_le_modulus χ hχ M)
      _ = _ := by ring
  · have he : Ioc M N = ∅ := Ioc_eq_empty_of_le (Nat.le_of_not_ge hMN)
    simp only [he, sum_empty, norm_zero]
    positivity

end TwinPrime.Analytic
