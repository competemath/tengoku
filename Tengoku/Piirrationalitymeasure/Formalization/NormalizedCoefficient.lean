import Tengoku.Piirrationalitymeasure.Formalization.PrincipalLaurent
import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The logarithmic coefficient in Proposition 2.7. The reduced coefficient
`c_0 / Phi` retains its power of two because `Phi` is coprime to ten.
-/

namespace PiIrrationality

noncomputable def normalizationMultiplier (n : ℕ) : ℚ :=
  (2 : ℚ) ^ (4 - 4645 * (n : ℤ)) * reducedLcm n

noncomputable def normalizedPiCoeff (n : ℕ) : ℚ :=
  -normalizationMultiplier n * laurentCoeffRat n 0 / 2

theorem reduced_constantCoeff_two_factor (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, laurentCoeffRat n 0 / (Phi n : ℚ) =
      (2 : ℚ) ^ (4645 * n - 1) * (z : ℚ) := by
  obtain ⟨q, hq⟩ := (reducedLcm_actual_laurent_integrality n hn).2.2
  obtain ⟨w, hw⟩ := principal_laurentCoeffRat_integer_factors n hn 0 (by omega)
  simp only [Nat.cast_zero, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
    Nat.reduceDiv] at hw
  let k := 4645 * n - 1
  let x : ℚ := laurentCoeffRat n 0 / (Phi n : ℚ) / 2 ^ k
  have hp : (Phi n : ℚ) ≠ 0 := by exact_mod_cast (Phi_pos n).ne'
  have ht : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  obtain ⟨z, hz⟩ := integer_of_Phi_and_ten_power n x
    (by
      refine ⟨(5 : ℤ) ^ (2 * n) * w, ?_⟩
      dsimp [x]
      rw [hw]
      change (Phi n : ℚ) * (2 ^ k * 5 ^ (2 * n) * (w : ℚ) / Phi n / 2 ^ k) = _
      push_cast
      field_simp)
    (by
      refine ⟨k, (5 : ℤ) ^ k * q, ?_⟩
      dsimp [x]
      rw [hq, show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
      push_cast
      field_simp)
  refine ⟨z, ?_⟩
  change laurentCoeffRat n 0 / (Phi n : ℚ) / 2 ^ k = (z : ℚ) at hz
  exact (div_eq_iff ht).mp hz |>.trans (mul_comm _ _)

theorem normalizedPiCoeff_formula (n : ℕ) :
    normalizedPiCoeff n =
      -(2 : ℚ) ^ (3 - 4645 * (n : ℤ)) * reducedLcm n * laurentCoeffRat n 0 := by
  unfold normalizedPiCoeff normalizationMultiplier
  rw [show (4 - 4645 * (n : ℤ)) = (3 - 4645 * (n : ℤ)) + 1 by omega,
    zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
  ring

theorem normalizedPiCoeff_is_integer (n : ℕ) (hn : 1 ≤ n) :
    ∃ V : ℤ, normalizedPiCoeff n = (V : ℚ) := by
  obtain ⟨z, hz⟩ := reduced_constantCoeff_two_factor n hn
  refine ⟨-4 * (lcmRange (7430 * n) : ℤ) * z, ?_⟩
  rw [normalizedPiCoeff_formula, reducedLcm]
  calc
    _ = -(2 : ℚ) ^ (3 - 4645 * (n : ℤ)) * (lcmRange (7430 * n) : ℚ) *
        (laurentCoeffRat n 0 / (Phi n : ℚ)) := by ring
    _ = -(2 : ℚ) ^ (3 - 4645 * (n : ℤ) + (4645 * n - 1 : ℕ)) *
        (lcmRange (7430 * n) : ℚ) * (z : ℚ) := by
      rw [hz, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
      ring
    _ = _ := by
      rw [show 3 - 4645 * (n : ℤ) + (4645 * n - 1 : ℕ) = 2 by omega]
      push_cast
      norm_num

end PiIrrationality
