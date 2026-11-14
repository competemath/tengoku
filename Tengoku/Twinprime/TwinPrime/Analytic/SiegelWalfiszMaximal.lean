import Tengoku.Twinprime.TwinPrime.Analytic.SiegelWalfisz
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterTrivialBounds
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform maximalization of a centered Siegel--Walfisz estimate

Short endpoints use an elementary centered bound. Longer endpoints have
comparable logarithms and lie above the uniform pointwise threshold.
Increasing the conductor exponent from `B` to `B+1` permits the pointwise
hypothesis there. This proves an implication, not Siegel--Walfisz itself.
-/

noncomputable section

open Finset Filter Classical

namespace TwinPrime.Analytic

/-- The elementary centered bound includes the principal character and zero.-/
theorem norm_centeredCharacterPsi_le_trivial {r : ℕ} (t : ℕ)
    (χ : DirichletCharacter ℂ r) :
    ‖centeredCharacterPsi t χ‖ ≤ (t : ℝ) * Real.log (t : ℝ) + t := by
  unfold centeredCharacterPsi
  apply (norm_sub_le _ _).trans
  apply add_le_add (norm_characterPsi_le t χ)
  split_ifs <;> simp

private theorem eventually_log_rpow_le_sqrt (a : ℝ) :
    ∀ᶠ T : ℕ in atTop, (Real.log (T : ℝ)) ^ a ≤ Real.sqrt (T : ℝ) := by
  have h := ((isLittleO_log_rpow_rpow_atTop a (s := 1 / 2) (by norm_num)).comp_tendsto
    tendsto_natCast_atTop_atTop).eventuallyLE
  filter_upwards [h, eventually_ge_atTop 2] with T hT hT2
  have hlog : 0 ≤ Real.log (T : ℝ) := Real.log_natCast_nonneg T
  simpa only [Function.comp_def, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog a),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg T) (1 / 2 : ℝ)),
    Real.sqrt_eq_rpow] using hT

private theorem short_centered_endpoint_le {r : ℕ} (A : ℝ) (t T : ℕ)
    (χ : DirichletCharacter ℂ r) (ht : t ≤ T) (hlog : 1 ≤ Real.log (T : ℝ))
    (hshort : (t : ℝ) ≤ (T : ℝ) / (Real.log (T : ℝ)) ^ (A + 2)) :
    ‖centeredCharacterPsi t χ‖ ≤ 2 * T / (Real.log (T : ℝ)) ^ A := by
  let L := Real.log (T : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL _
  have hL2 : 0 < L ^ (2 : ℕ) := pow_pos hL _
  calc
    _ ≤ (t : ℝ) * Real.log (t : ℝ) + t := norm_centeredCharacterPsi_le_trivial t χ
    _ ≤ (t : ℝ) * (L + 1) := by
      have hmono := mul_le_mul_of_nonneg_left (log_natCast_mono ht) (Nat.cast_nonneg t)
      dsimp only [L]
      linarith
    _ ≤ ((T : ℝ) / L ^ (A + 2)) * (L + 1) :=
      mul_le_mul_of_nonneg_right hshort (by linarith)
    _ = ((T : ℝ) / L ^ A) * ((L + 1) / L ^ (2 : ℕ)) := by
      rw [Real.rpow_add hL, Real.rpow_two]
      field_simp
    _ ≤ ((T : ℝ) / L ^ A) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_iff₀ hL2).mpr
      nlinarith
    _ = _ := by dsimp only [L]; ring

/-- A uniform centered pointwise Siegel--Walfisz estimate gives the full
finite endpoint maximum, including primitive conductor one.-/
theorem PointwiseSiegelWalfisz.maximal (hSW : PointwiseSiegelWalfisz) :
    MaximalSiegelWalfisz := by
  intro A B hA hB
  obtain ⟨C, hC, T₀, hT₀, hpoint⟩ := hSW A (B + 1) hA (by linarith)
  let K : ℝ := max 2 (C * (2 : ℝ) ^ A)
  have hK : 0 < K := (by norm_num : (0 : ℝ) < 2).trans_le (le_max_left _ _)
  have hloglim : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ T : ℕ in atTop,
      1 ≤ Real.log (T : ℝ) ∧ 2 * (2 : ℝ) ^ B ≤ Real.log (T : ℝ) ∧
        (Real.log (T : ℝ)) ^ (A + 2) ≤ Real.sqrt (T : ℝ) ∧ T₀ ^ 2 ≤ T := by
    filter_upwards [hloglim.eventually (eventually_ge_atTop 1),
      hloglim.eventually (eventually_ge_atTop (2 * (2 : ℝ) ^ B)),
      eventually_log_rpow_le_sqrt (A + 2), eventually_ge_atTop (T₀ ^ 2)] with T h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨K, hK, max 2 N, le_max_left _ _, ?_⟩
  intro T hT r hr hcond χ hχ
  obtain ⟨hL1, hLB, hpow, hthreshold⟩ := hN T ((le_max_right _ _).trans hT)
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hL0 : 0 < Real.log (T : ℝ) := zero_lt_one.trans_le hL1
  have hden : 0 < (Real.log (T : ℝ)) ^ (A + 2) := Real.rpow_pos_of_pos hL0 _
  have hdenA : 0 < (Real.log (T : ℝ)) ^ A := Real.rpow_pos_of_pos hL0 _
  have hH : Real.sqrt (T : ℝ) ≤ (T : ℝ) / (Real.log (T : ℝ)) ^ (A + 2) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ Real.sqrt (T : ℝ) * Real.sqrt (T : ℝ) :=
        mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
      _ = _ := by rw [← pow_two, Real.sq_sqrt hT0.le]
  have hT₀sqrt : (T₀ : ℝ) ≤ Real.sqrt (T : ℝ) := by
    calc
      _ = Real.sqrt ((T₀ : ℝ) ^ (2 : ℕ)) := (Real.sqrt_sq (Nat.cast_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by exact_mod_cast hthreshold)
  unfold characterMaxError
  apply Finset.sup'_le
  intro t ht
  have htT : t ≤ T := by have := mem_range.mp ht; omega
  by_cases hshort : (t : ℝ) ≤ (T : ℝ) / (Real.log (T : ℝ)) ^ (A + 2)
  · apply (short_centered_endpoint_le A t T χ htT hL1 hshort).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg T)) hdenA.le
  · have hsqrtt : Real.sqrt (T : ℝ) ≤ (t : ℝ) := hH.trans (lt_of_not_ge hshort).le
    have htthreshold : T₀ ≤ t := by exact_mod_cast hT₀sqrt.trans hsqrtt
    have ht2 : 2 ≤ t := hT₀.trans htthreshold
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hlt0 : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht2)
    have hhalf : Real.log (T : ℝ) ≤ 2 * Real.log (t : ℝ) := by
      have h := Real.log_le_log (Real.sqrt_pos.mpr hT0) hsqrtt
      rw [Real.log_sqrt hT0.le] at h
      linarith
    have hBpow : (Real.log (T : ℝ)) ^ B ≤
        (2 : ℝ) ^ B * (Real.log (t : ℝ)) ^ B := by
      exact (Real.rpow_le_rpow hL0.le hhalf hB.le).trans_eq (Real.mul_rpow (by norm_num) hlt0.le)
    have hcondt : (r : ℝ) ≤ (Real.log (t : ℝ)) ^ (B + 1) := by
      apply hcond.trans
      calc
        _ ≤ (2 : ℝ) ^ B * (Real.log (t : ℝ)) ^ B := hBpow
        _ ≤ Real.log (t : ℝ) * (Real.log (t : ℝ)) ^ B :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hlt0.le _)
        _ = _ := by rw [Real.rpow_add hlt0, Real.rpow_one]; ring
    have hApow : (Real.log (T : ℝ)) ^ A ≤
        (2 : ℝ) ^ A * (Real.log (t : ℝ)) ^ A :=
      (Real.rpow_le_rpow hL0.le hhalf hA.le).trans_eq (Real.mul_rpow (by norm_num) hlt0.le)
    have htden : 0 < (Real.log (t : ℝ)) ^ A := Real.rpow_pos_of_pos hlt0 _
    calc
      _ ≤ C * t / (Real.log (t : ℝ)) ^ A := hpoint t htthreshold r hr hcondt χ hχ
      _ ≤ C * T / (Real.log (t : ℝ)) ^ A := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast htT) hC.le) htden.le
      _ ≤ (C * (2 : ℝ) ^ A) * T / (Real.log (T : ℝ)) ^ A := by
        apply (div_le_div_iff₀ htden hdenA).mpr
        calc
          _ ≤ (C * T) * ((2 : ℝ) ^ A * (Real.log (t : ℝ)) ^ A) :=
            mul_le_mul_of_nonneg_left hApow (by positivity)
          _ = _ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg T)) hdenA.le

end TwinPrime.Analytic
