import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.Complete
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma654.KummerCriterion
import Tengoku.Seed.NumberTheory.MulChar.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Every value of a complex multiplicative character has norm at most one.
@isnad1 id=le.0h3v.s6.e39855a80220 from=translated src=- shape=4b09d837 vocab=122ff3e2
-/
theorem mulChar_norm_le_one (chi : MulChar F ℂ) (x : F) : ‖chi x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · letI : NeZero (orderOf chi) := ⟨chi.orderOf_pos.ne'⟩
    obtain ⟨zeta, hzeta, heq⟩ := chi.apply_mem_rootsOfUnity_orderOf hx
    rw [← heq, Complex.norm_eq_one_of_mem_rootsOfUnity hzeta]

/-- Character-weighted power fibers recover the character value. Summing
all nonzero twists avoids choosing representatives of the power cosets.
@isnad1 id=eq.3h4v.s9.ea36f6b6048b from=translated src=- shape=719d215b vocab=7fe4c77c
-/
theorem character_weighted_power_fibers
    {m : ℕ} (hm : 0 < m) (chi : MulChar F ℂ) (hchi : chi ≠ 1) (hpow : chi ^ m = 1)
    (z : F) :
    (∑ a : F, chi a * ((Finset.univ.filter (fun y : F => y ^ m = a⁻¹ * z)).card : ℂ)) =
      ((Fintype.card F : ℂ) - 1) * chi z := by
  have hweight (a y : F) : (if y ^ m = a⁻¹ * z then chi a else 0) =
      if a * y ^ m = z then chi a else 0 := by
    by_cases ha : a = 0
    · simp [ha, MulChar.map_zero]
    · have he : y ^ m = a⁻¹ * z ↔ a * y ^ m = z := by
        constructor
        · intro h
          rw [h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
        · intro h
          rw [← h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      simp only [he]
  have hinner (y : F) : (∑ a : F, if a * y ^ m = z then chi a else 0) =
      if y = 0 then 0 else chi z := by
    by_cases hy : y = 0
    · subst y
      simp only [zero_pow (Nat.ne_of_gt hm), mul_zero ]
      by_cases hz : z = 0
      · simp only [hz, ite_true]
        exact MulChar.sum_eq_zero_of_ne_one hchi
      · simp [Ne.symm hz]
    · rw [ite_eq_right hy]
      have hym : y ^ m ≠ 0 := pow_ne_zero m hy
      have hval : chi (y ^ m) = 1 := by
        rw [map_pow, ← chi.pow_apply' (Nat.ne_of_gt hm), hpow]
        exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)
      have heq (a : F) : a * y ^ m = z ↔ a = z / y ^ m :=
        (eq_div_iff hym).symm
      simp_rw [heq]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      have hinv : chi (y ^ m)⁻¹ = 1 := by
        have hh := congrArg chi (mul_inv_cancel₀ hym)
        simpa only [map_mul, hval, one_mul, map_one] using hh
      rw [div_eq_mul_inv, map_mul, hinv, mul_one]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  simp_rw [hweight]
  rw [Finset.sum_comm]
  simp_rw [hinner]
  have hsum : (∑ y : F, if y = 0 then chi z else 0) = chi z := by simp
  have htotal : (∑ y : F, if y = 0 then 0 else chi z) =
      (∑ _y : F, chi z) - chi z := by
    have h := Finset.sum_add_distrib (s := (Finset.univ : Finset F))
      (f := fun y => if y = 0 then chi z else 0)
      (g := fun y => if y = 0 then 0 else chi z)
    simp only [ite_add_ite, add_zero, zero_add, ite_self, hsum] at h
    linear_combination -h
  rw [htotal]
  simp [sub_mul]

/-- The character sum is an average of centered point counts of the
nonzero constant twists of the Kummer equation.
@isnad1 id=eq.3h4v.s9.e058c29ee0cb from=translated src=- shape=30a63a10 vocab=ad75a6ba
-/
theorem character_sum_eq_weighted_twist_counts
    {m : ℕ} (hm : 0 < m) (chi : MulChar F ℂ) (hchi : chi ≠ 1) (hpow : chi ^ m = 1)
    (f : Polynomial F) :
    ((Fintype.card F : ℂ) - 1) * (∑ x : F, chi (f.eval x)) =
      ∑ a : F, chi a * ((stepanovSolutionCount m (C a⁻¹ * f) : ℂ) - Fintype.card F) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hz : (∑ a : F, chi a * (Fintype.card F : ℂ)) = 0 := by
    rw [← Finset.sum_mul, MulChar.sum_eq_zero_of_ne_one hchi, zero_mul]
  rw [hz, sub_zero, Finset.mul_sum]
  simp_rw [stepanovSolutionCount_eq_sum, Nat.cast_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  exact (character_weighted_power_fibers hm chi hchi hpow (f.eval x)).symm

end MagicSquares.LN97
