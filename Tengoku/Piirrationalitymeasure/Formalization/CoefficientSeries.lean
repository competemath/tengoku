import Tengoku.Piirrationalitymeasure.Formalization.Coefficient
import Tengoku.Seed.RingTheory.PowerSeries.WellKnown

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual formal generating series (4.4) and positive coefficients (4.8). -/

namespace PiIrrationality

open PowerSeries

noncomputable def PSeriesNat : PowerSeries ℕ := 2 + 6 * X + 9 * X ^ 2 + 6 * X ^ 3 + 2 * X ^ 4

noncomputable def SNumeratorNat : PowerSeries ℕ := (1 + X) ^ 3714 * PSeriesNat ^ 3714

noncomputable def PSeries : PowerSeries ℚ := 2 + 6 * X + 9 * X ^ 2 + 6 * X ^ 3 + 2 * X ^ 4

noncomputable def SNumerator : PowerSeries ℚ :=
  PowerSeries.map (Nat.castRingHom ℚ) SNumeratorNat

noncomputable def Sseries : PowerSeries ℚ :=
  SNumerator * (invOneSubPow ℚ 7430).val

/--
@isnad1 id=eq.0h0v.s8.746fcfdd3a2c from=translated src=- shape=7fd5f4a4 vocab=ad07db73
-/
theorem PSeries_factorization :
    PSeries = (X ^ 2 + 2 * X + 2) * (2 * X ^ 2 + 2 * X + 1) := by
  unfold PSeries
  ring

/--
@isnad1 id=eq.0h0v.s6.f6437962a73e from=translated src=- shape=29426fae vocab=92cca752
-/
theorem SNumerator_eq : SNumerator = (1 + X) ^ 3714 * PSeries ^ 3714 := by
  simp only [SNumerator, SNumeratorNat, PSeriesNat, PSeries, map_add, map_mul,
    map_pow, map_one, map_ofNat, PowerSeries.map_X]

/--
@isnad1 id=eq.0h0v.s5.9fae7c8416f9 from=translated src=- shape=a6b805a1 vocab=6ee514a0
-/
theorem SNumerator_constantCoeff : constantCoeff SNumerator = (2 : ℚ) ^ 3714 := by
  simp [SNumerator_eq, PSeries, map_ofNat]

/--
@isnad1 id=le.0h2v.s6.4035b23fd9e3 from=translated src=- shape=caca8ec8 vocab=ee1ef8f1
-/
theorem SNumerator_pow_coeff_nonneg (n k : ℕ) : 0 ≤ coeff k (SNumerator ^ n) := by
  rw [SNumerator, ← map_pow, coeff_map]
  exact Nat.cast_nonneg _

/--
@isnad1 id=lt.0h1v.s6.428f1720516f from=translated src=- shape=3a3fef96 vocab=0bb89190
-/
theorem SNumerator_pow_constantCoeff_pos (n : ℕ) : 0 < coeff 0 (SNumerator ^ n) := by
  rw [coeff_zero_eq_constantCoeff, map_pow, SNumerator_constantCoeff]
  positivity

/--
@isnad1 id=eq.0h2v.s6.e1685dea3377 from=translated src=- shape=4992463d vocab=0b932e99
-/
theorem invOneSubPow_pow (d n : ℕ) :
    (invOneSubPow ℚ d).val ^ n = (invOneSubPow ℚ (d * n)).val := by
  have h : invOneSubPow ℚ d ^ n = invOneSubPow ℚ (d * n) := by
    simp only [invOneSubPow_eq_inv_one_sub_pow, pow_mul]
  exact congrArg Units.val h

/--
@isnad1 id=eq.0h1v.s6.8a25ff28482d from=translated src=- shape=1b0a8150 vocab=b33d35c3
-/
theorem Sseries_pow_eq (n : ℕ) :
    Sseries ^ n = SNumerator ^ n * (invOneSubPow ℚ (7430 * n)).val := by
  rw [Sseries, mul_pow, invOneSubPow_pow]

/--
@isnad1 id=lt.1h2v.s6.69eea65fbfe3 from=translated src=- shape=a01e5b35 vocab=945eeee8
-/
theorem inversePower_coeff_pos {d : ℕ} (hd : 0 < d) (k : ℕ) :
    0 < coeff k (invOneSubPow ℚ d).val := by
  rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℚ d hd, coeff_mk]
  exact_mod_cast Nat.choose_pos (show d - 1 ≤ d - 1 + k by omega)

/--
@isnad1 id=lt.1h2v.s7.539d8e095b56 from=translated src=- shape=f4fd29cb vocab=779d98bb
-/
theorem Sseries_pow_coeff_pos {n : ℕ} (hn : 0 < n) (k : ℕ) :
    0 < coeff k (Sseries ^ n) := by
  rw [Sseries_pow_eq, coeff_mul]
  apply Finset.sum_pos'
  · intro p hp
    exact mul_nonneg (SNumerator_pow_coeff_nonneg n p.1)
      (inversePower_coeff_pos (by omega : 0 < 7430 * n) p.2).le
  · refine ⟨(0, k), by simp, ?_⟩
    exact mul_pos (SNumerator_pow_constantCoeff_pos n)
      (inversePower_coeff_pos (by omega : 0 < 7430 * n) k)

/--
@isnad1 id=lt.0h1v.s6.3d47231b73fe from=translated src=- shape=4be17f24 vocab=6c067a8d
-/
theorem Sseries_coeff_pos (k : ℕ) : 0 < coeff k Sseries := by
  simpa only [pow_one] using Sseries_pow_coeff_pos (by norm_num : 0 < 1) k

/--
@isnad1 id=eq.0h0v.s7.714a50afcf98 from=translated src=- shape=bd7d9bc3 vocab=ada097e9
-/
theorem Sseries_clearing_identity :
    Sseries * (1 - X) ^ 7430 = (1 + X) ^ 3714 * PSeries ^ 3714 := by
  rw [Sseries, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow ℚ 7430,
    (invOneSubPow ℚ 7430).val_inv, mul_one, SNumerator_eq]

/--
@isnad1 id=eq.0h1v.s7.26a1340fd8c3 from=translated src=- shape=1f6bcc52 vocab=ada097e9
-/
theorem Sseries_pow_clearing_identity (n : ℕ) :
    Sseries ^ n * (1 - X) ^ (7430 * n) =
      (1 + X) ^ (3714 * n) * PSeries ^ (3714 * n) := by
  have h := congrArg (fun f : PowerSeries ℚ => f ^ n) Sseries_clearing_identity
  simpa only [mul_pow, ← pow_mul] using h

end PiIrrationality
