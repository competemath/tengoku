import Tengoku.Twinprime.TwinPrime.Analytic.CharacterSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Centered character errors and their finite endpoint maxima

The principal character has the linear main term subtracted. All other
characters retain their uncentered sum. The progression maximum is bounded
by a sum of character maxima; no mean-value estimate is assumed or proved here.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

def centeredCharacterPsi {q : ℕ} (t : ℕ) (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact characterPsi t χ - if χ = 1 then (t : ℂ) else 0

def characterMaxError {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (range (T + 1)).sup' ⟨0, mem_range.mpr (Nat.succ_pos T)⟩
    (fun t => ‖centeredCharacterPsi t χ‖)

theorem characterMaxError_nonneg {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ characterMaxError T χ :=
  (norm_nonneg _).trans (Finset.le_sup' (f := fun t => ‖centeredCharacterPsi t χ‖)
    (mem_range.mpr (Nat.succ_pos T) : 0 ∈ range (T + 1)))

theorem norm_centeredCharacterPsi_le_max {q t T : ℕ}
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖centeredCharacterPsi t χ‖ ≤ characterMaxError T χ :=
  Finset.le_sup' (f := fun t => ‖centeredCharacterPsi t χ‖) (mem_range.mpr (by omega))

theorem totient_mul_progressionError_eq_centeredCharacter_sum (t q a : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) :
    (Nat.totient q : ℂ) * (progressionError t q a : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * centeredCharacterPsi t χ := by
  classical
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hua : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hu : IsUnit ((a : ZMod q)⁻¹) := by
    obtain ⟨u, hu⟩ := hua
    rw [← hu, ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have hp : (∑ χ : DirichletCharacter ℂ q,
      χ ((a : ZMod q)⁻¹) * (if χ = 1 then (t : ℂ) else 0)) = t := by
    simp [mul_ite, MulChar.one_apply hu]
  symm
  calc
    _ = (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * characterPsi t χ) - t := by
      simp only [centeredCharacterPsi, mul_sub, sum_sub_distrib, hp]
    _ = _ := by
      rw [← totient_mul_progressionPsi_eq_character_sum t q a hq ha]
      unfold progressionError
      push_cast
      field_simp

theorem abs_progressionError_le_character_sum (t q a : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) :
    |progressionError t q a| ≤
      (∑ χ : DirichletCharacter ℂ q, ‖centeredCharacterPsi t χ‖) / Nat.totient q := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hφ).mpr
  have hn := congrArg norm (totient_mul_progressionError_eq_centeredCharacter_sum t q a hq ha)
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [mul_comm, hn]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro χ _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans_eq (one_mul _)

/-- Both the residue and integer-endpoint maxima are controlled uniformly.-/
theorem progressionMaxError_le_characterMaxError (T q : ℕ) (hq : 0 < q) :
    progressionMaxError T q ≤
      (∑ χ : DirichletCharacter ℂ q, characterMaxError T χ) / Nat.totient q := by
  unfold progressionMaxError
  apply Finset.sup'_le
  intro ta hta
  split_ifs with hgood
  · have ht : ta.1 ≤ T := by have := mem_range.mp (mem_product.mp hta).1; omega
    apply (abs_progressionError_le_character_sum ta.1 q ta.2 hq hgood.2).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact sum_le_sum fun χ _ => norm_centeredCharacterPsi_le_max χ ht
  · exact div_nonneg (sum_nonneg fun χ _ => characterMaxError_nonneg T χ) (Nat.cast_nonneg _)

end TwinPrime.Analytic
