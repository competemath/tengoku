import Tengoku.Piirrationalitymeasure.Formalization.EvenPoleIdentification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact even partial fractions with the actual derivative-defined coefficients. -/

namespace PiIrrationality.EvenPole

open Polynomial

noncomputable def density {K : Type*} [Field K] [Algebra ℚ K]
    (F : Polynomial ℤ) (m : ℕ) (t : K) : K :=
  aeval t (numerator F) / (25 - t ^ 2) ^ m

theorem partialFractions_lowIndex {K : Type*} [Field K] [Algebra ℚ K]
    (F : Polynomial ℤ) {m : ℕ} (hm : 0 < m) (t : K)
    (htplus : t + 5 ≠ 0) (htminus : t - 5 ≠ 0) :
    density F m t = aeval t (part F m) +
      (∑ i : Fin m, (localCoeff F m i.val : K) / (t + 5) ^ (m - i.val)) +
      (∑ i : Fin m, (localCoeff F m i.val : K) / (5 - t) ^ (m - i.val)) := by
  let : CharZero K := algebraRat.charZero K
  let D := (t + 5) ^ m * (t - 5) ^ m
  have hD : D ≠ 0 := mul_ne_zero (pow_ne_zero _ htplus) (pow_ne_zero _ htminus)
  have hleft (i : Fin m) : (localCoeff F m i.val : K) / (t + 5) ^ (m - i.val) * D =
      (localCoeff F m i.val : K) * (t + 5) ^ i.val * (t - 5) ^ m :=
    pole_power_cancel m i.val (Nat.le_of_lt i.isLt) (t + 5) (t - 5) _ htplus
  have hright (i : Fin m) : (localCoeff F m i.val : K) / (5 - t) ^ (m - i.val) * D =
      ((-1 : K) ^ (i.val + m) * localCoeff F m i.val) *
        (t - 5) ^ i.val * (t + 5) ^ m := by
    have hsign : (-1 : K) ^ (i.val + m) = (-1 : K) ^ (m - i.val) := by
      rw [show i.val + m = (m - i.val) + 2 * i.val by have := i.isLt; omega,
        pow_add, pow_mul]
      norm_num
    rw [show 5 - t = -(t - 5) by ring, div_neg_power, ← hsign]
    simpa only [D, mul_comm ((t + 5) ^ m) ((t - 5) ^ m)] using
      pole_power_cancel m i.val (Nat.le_of_lt i.isLt) (t - 5) (t + 5)
        ((-1 : K) ^ (i.val + m) * localCoeff F m i.val) htminus
  have h := (actual_decomposition F hm).eval t
  push_cast at h
  apply mul_right_cancel₀ hD
  rw [density, show 25 - t ^ 2 = -((t + 5) * (t - 5)) by ring,
    div_neg_power, mul_pow, div_mul_cancel₀ _ hD]
  rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
  simp_rw [hleft, hright]
  exact h

theorem partialFractions {K : Type*} [Field K] [Algebra ℚ K]
    (F : Polynomial ℤ) {m : ℕ} (hm : 0 < m) (t : K)
    (htplus : t + 5 ≠ 0) (htminus : t - 5 ≠ 0) :
    density F m t = aeval t (part F m) +
      ∑ j : Fin m, (laurentCoeff F m (j.val : ℤ) : K) *
        (1 / (5 + t) ^ (j.val + 1) + 1 / (5 - t) ^ (j.val + 1)) := by
  rw [partialFractions_lowIndex F hm t htplus htminus, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib, ← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply]
  have hindex : ((m : ℤ) - 1 - j.val).toNat = j.rev.val := by
    simp only [Fin.val_rev]
    have := j.isLt
    omega
  have hpower : m - j.rev.val = j.val + 1 := by
    rw [Fin.val_rev]
    have := j.isLt
    omega
  have hj : (j.val : ℤ) < m := by exact_mod_cast j.isLt
  rw [laurentCoeff, ite_eq_left hj, hindex, hpower, add_comm t 5]
  ring

end PiIrrationality.EvenPole
