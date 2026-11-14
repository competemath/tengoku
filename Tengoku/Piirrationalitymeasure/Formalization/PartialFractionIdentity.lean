import Tengoku.Piirrationalitymeasure.Formalization.LaurentIdentification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The complete even partial-fraction identity (2.2), over any field containing
the rationals. In particular the same proved coefficients apply over `R`
and `C` in the subsequent derivative and contour-integral arguments.
-/

namespace PiIrrationality

open Polynomial

theorem pole_power_cancel {K : Type*} [Field K]
    (m i : ℕ) (hi : i ≤ m) (x y c : K) (hx : x ≠ 0) :
    c / x ^ (m - i) * (x ^ m * y ^ m) = c * x ^ i * y ^ m := by
  rw [show x ^ m = x ^ (m - i) * x ^ i by rw [← pow_add, Nat.sub_add_cancel hi]]
  field_simp

theorem div_neg_power {K : Type*} [Field K] (c x : K) (m : ℕ) :
    c / (-x) ^ m = (-1) ^ m * c / x ^ m := by
  rw [div_eq_mul_inv, ← inv_pow, inv_neg, neg_pow x⁻¹ m, inv_pow]
  ring

theorem rationalFunction_partialFractions_lowIndex {K : Type*} [Field K] [Algebra ℚ K]
    (n : ℕ) (t : K) (htplus : t + 5 ≠ 0) (htminus : t - 5 ≠ 0) :
    5 * t ^ (2 * 1857 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) /
        (25 - t ^ 2) ^ (5570 * n + 1) =
      aeval t (polynomialPart n) +
        (∑ i : Fin (5570 * n + 1),
          (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : K) /
            (t + 5) ^ (5570 * n + 1 - i.val)) +
        (∑ i : Fin (5570 * n + 1),
          (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : K) /
            (5 - t) ^ (5570 * n + 1 - i.val)) := by
  let : CharZero K := algebraRat.charZero K
  let m := 5570 * n + 1
  let D := (t + 5) ^ m * (t - 5) ^ m
  have hD : D ≠ 0 := mul_ne_zero (pow_ne_zero _ htplus) (pow_ne_zero _ htminus)
  have hodd : Odd m := ⟨2785 * n, by dsimp [m]; omega⟩
  have hden : (25 - t ^ 2) ^ m = -D := by
    rw [show 25 - t ^ 2 = -((t + 5) * (t - 5)) by ring, hodd.neg_pow, mul_pow]
  have hleft (i : Fin m) :
      (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : K) /
          (t + 5) ^ (m - i.val) * D =
        (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : K) *
          (t + 5) ^ i.val * (t - 5) ^ m :=
    pole_power_cancel m i.val (Nat.le_of_lt i.isLt) (t + 5) (t - 5) _ htplus
  have hright (i : Fin m) :
      (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : K) /
          (5 - t) ^ (m - i.val) * D =
        ((-1 : K) ^ (i.val + m) * laurentCoeffRat n (5570 * (n : ℤ) - i.val)) *
          (t - 5) ^ i.val * (t + 5) ^ m := by
    have hsign : (-1 : K) ^ (i.val + m) = (-1 : K) ^ (m - i.val) := by
      rw [show i.val + m = (m - i.val) + 2 * i.val by have := i.isLt; omega,
        pow_add, pow_mul]
      norm_num
    rw [show 5 - t = -(t - 5) by ring, div_neg_power, ← hsign]
    simpa only [D, mul_comm ((t + 5) ^ m) ((t - 5) ^ m)] using
      pole_power_cancel m i.val (Nat.le_of_lt i.isLt) (t - 5) (t + 5)
        ((-1 : K) ^ (i.val + m) * laurentCoeffRat n (5570 * (n : ℤ) - i.val)) htminus
  have h := (actual_twoPoleDecomposition n).eval n _ _ t
  push_cast at h
  apply mul_right_cancel₀ hD
  change (5 * t ^ (2 * 1857 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) /
    (25 - t ^ 2) ^ m) * D = _
  rw [hden, div_neg, neg_mul, div_mul_cancel₀ _ hD]
  rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
  dsimp only [m] at hleft hright
  simp_rw [hleft, hright]
  exact h

theorem rationalFunction_partialFractions {K : Type*} [Field K] [Algebra ℚ K]
    (n : ℕ) (t : K) (htplus : t + 5 ≠ 0) (htminus : t - 5 ≠ 0) :
    5 * t ^ (2 * 1857 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) /
        (25 - t ^ 2) ^ (5570 * n + 1) =
      aeval t (polynomialPart n) +
        ∑ j : Fin (5570 * n + 1), (laurentCoeffRat n (j.val : ℤ) : K) *
          (1 / (5 + t) ^ (j.val + 1) + 1 / (5 - t) ^ (j.val + 1)) := by
  rw [rationalFunction_partialFractions_lowIndex n t htplus htminus, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply]
  have hindex : 5570 * (n : ℤ) - (j.rev.val : ℤ) = (j.val : ℤ) := by
    simp only [Fin.val_rev]
    have := j.isLt
    omega
  have hpower : 5570 * n + 1 - j.rev.val = j.val + 1 := by
    rw [Fin.val_rev]
    have := j.isLt
    omega
  rw [hindex, hpower, add_comm t 5]
  ring

end PiIrrationality
