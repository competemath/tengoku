import Tengoku.Piirrationalitymeasure.Formalization.PolynomialLaurent
import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The coefficient denominator clearing for the second representation of
Lemma 2.5. The scaled antiderivative coefficient is an ordinary integer.
-/

namespace PiIrrationality

/--
@isnad1 id=eq.1h2v.s6.4c23d7556962 from=translated src=- shape=4bb39eb4 vocab=07a0524e
-/
theorem choose_div_succ_eq_choose_div (j q : ℕ) (hj : 0 < j) :
    ((j + q).choose q : ℚ) / (q + 1) = ((j + q).choose (q + 1) : ℚ) / j := by
  have h : ((j + q).choose (q + 1) : ℚ) * (q + 1 : ℚ) =
      ((j + q).choose q : ℚ) * (j : ℚ) := by
    exact_mod_cast (by simpa using Nat.choose_succ_right_eq (j + q) q)
  have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj.ne'
  have hqQ : (q + 1 : ℚ) ≠ 0 := by positivity
  field_simp
  simpa only [mul_comm] using h.symm

/--
@isnad1 id=ex.2h2v.s7.ce150a12ae50 from=translated src=- shape=bc7940b2 vocab=117348ea
-/
theorem polynomial_negative_laurent_scaled_is_integer
    (n : ℕ) (hn : 1 ≤ n) (q : ℕ) (hq : q < 7430 * n - 1) :
    ∃ z : ℤ, (10 : ℚ) ^ (q + 1) * reducedLcm n *
      laurentCoeffRat n (-((q + 1 : ℕ) : ℤ)) / (q + 1) = (z : ℚ) := by
  obtain ⟨z, hz⟩ := (reducedLcm_actual_laurent_integrality n hn).2.1
    (-((q + 1 : ℕ) : ℤ)) (by omega) (by omega) (by omega)
  simp only [neg_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast] at hz
  refine ⟨-z, ?_⟩
  rw [Int.cast_neg, ← hz]
  simp only [div_neg, neg_neg]
  push_cast
  ring

/--
@isnad1 id=ex.2h2v.s6.a815c3eb0702 from=translated src=- shape=7604d1ae vocab=71eed312
-/
theorem polynomial_zero_laurent_div_is_integer
    (n : ℕ) (hn : 1 ≤ n) (q : ℕ) (hq : q < 7430 * n - 1) :
    ∃ z : ℤ, reducedLcm n * laurentCoeffRat n 0 / (q + 1) = (z : ℚ) := by
  obtain ⟨z, hz⟩ := (reducedLcm_actual_laurent_integrality n hn).2.2
  obtain ⟨l, hl⟩ := dvd_lcmRange (7430 * n) (q + 1) (by omega) (by omega)
  have hlQ : (lcmRange (7430 * n) : ℚ) = (q + 1 : ℚ) * (l : ℚ) := by
    exact_mod_cast hl
  have hqQ : (q + 1 : ℚ) ≠ 0 := by positivity
  refine ⟨(l : ℤ) * z, ?_⟩
  unfold reducedLcm
  rw [hlQ]
  calc
    _ = (l : ℚ) * (laurentCoeffRat n 0 / (Phi n : ℚ)) := by field_simp
    _ = _ := by rw [hz]; push_cast; rfl

/--
@isnad1 id=ex.3h3v.s7.c753ffb15aec from=translated src=- shape=f7a3efe4 vocab=ec0640b5
-/
theorem polynomial_laurent_correction_scaled_is_integer
    (n : ℕ) (hn : 1 ≤ n) (q : ℕ) (hq : q < 7430 * n - 1)
    (j : ℕ) (hj : j ≤ 5570 * n) :
    ∃ z : ℤ, (10 : ℚ) ^ (q + 1) * reducedLcm n *
      (((j + q).choose q : ℚ) * laurentCoeffRat n (j : ℤ) / 10 ^ (j + q + 1)) /
        (q + 1) = (z : ℚ) := by
  by_cases hj0 : j = 0
  · subst j
    obtain ⟨z, hz⟩ := polynomial_zero_laurent_div_is_integer n hn q hq
    refine ⟨z, ?_⟩
    rw [← hz]
    norm_num only [zero_add, Nat.choose_self, Nat.cast_one, Nat.cast_zero, one_mul]
    field_simp
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    obtain ⟨z, hz⟩ := (reducedLcm_actual_laurent_integrality n hn).2.1
      (j : ℤ) (by omega) (by exact_mod_cast hj) (by exact_mod_cast hj0)
    refine ⟨((j + q).choose (q + 1) : ℤ) * z, ?_⟩
    have hqQ : (q + 1 : ℚ) ≠ 0 := by positivity
    have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0
    calc
      _ = (((j + q).choose q : ℚ) / (q + 1)) *
          (reducedLcm n * ((10 : ℚ) ^ (-(j : ℤ)) * laurentCoeffRat n (j : ℤ))) := by
        rw [show j + q + 1 = j + (q + 1) by omega, pow_add, zpow_neg, zpow_natCast]
        field_simp
        ring
      _ = ((j + q).choose (q + 1) : ℚ) *
          (reducedLcm n * ((10 : ℚ) ^ (-(j : ℤ)) * laurentCoeffRat n (j : ℤ)) / j) := by
        rw [choose_div_succ_eq_choose_div j q hjpos]
        ring
      _ = _ := by rw [show ((j : ℤ) : ℚ) = (j : ℚ) by simp] at hz; rw [hz]; push_cast; rfl

noncomputable def poleAntiderivativeScaledCoeff (n q : ℕ) : ℚ :=
  (10 : ℚ) ^ (q + 1) * reducedLcm n * (poleShiftCoeff n q : ℚ) / (q + 1)

/--
@isnad1 id=ex.2h2v.s5.66c5b8d10fd4 from=translated src=- shape=89be9138 vocab=0804c443
-/
theorem poleAntiderivativeScaledCoeff_is_integer
    (n : ℕ) (hn : 1 ≤ n) (q : ℕ) (hq : q < 7430 * n - 1) :
    ∃ z : ℤ, poleAntiderivativeScaledCoeff n q = (z : ℚ) := by
  obtain ⟨a, ha⟩ := polynomial_negative_laurent_scaled_is_integer n hn q hq
  choose z hz using fun j : Fin (5570 * n + 1) =>
    polynomial_laurent_correction_scaled_is_integer n hn q hq j.val
      (Nat.le_of_lt_succ j.isLt)
  refine ⟨a - ∑ j : Fin (5570 * n + 1), z j, ?_⟩
  unfold poleAntiderivativeScaledCoeff
  rw [poleShiftCoeff_laurent_formula, mul_sub, sub_div, Finset.mul_sum, Finset.sum_div, ha]
  simp_rw [hz]
  push_cast
  rfl

end PiIrrationality
