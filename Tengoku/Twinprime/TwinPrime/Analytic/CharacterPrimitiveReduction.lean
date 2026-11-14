import Tengoku.Twinprime.TwinPrime.Analytic.CharacterMaximal
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterExceptions
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterExceptionGrowth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Primitive character replacement with maximal endpoints retained

An induced character is principal exactly when its primitive character is
principal. Thus centering does not introduce an extra main term in the
replacement. The final finite reduction keeps the inducing-character
multiplicities explicit; it does not yet regroup them by conductor.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

theorem primitiveCharacter_principal_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  · intro h
    subst χ
    exact DirichletCharacter.primitiveCharacter_one

theorem norm_centeredCharacterPsi_sub_primitive_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℕ) :
    ‖centeredCharacterPsi t χ - centeredCharacterPsi t χ.primitiveCharacter‖ ≤
      noncoprimeMangoldtMass t q := by
  classical
  have heq : centeredCharacterPsi t χ - centeredCharacterPsi t χ.primitiveCharacter =
      characterPsi t χ - characterPsi t χ.primitiveCharacter := by
    simp only [centeredCharacterPsi, primitiveCharacter_principal_iff]
    ring_nf
  rw [heq]
  exact norm_characterPsi_sub_primitive_le χ t

theorem characterMaxError_le_primitive {q : ℕ} [NeZero q]
    (T : ℕ) (χ : DirichletCharacter ℂ q) :
    characterMaxError T χ ≤ characterMaxError T χ.primitiveCharacter + noncoprimeMangoldtMass T q := by
  unfold characterMaxError at ⊢
  apply Finset.sup'_le
  intro t ht
  have htT : t ≤ T := by have := mem_range.mp ht; omega
  calc
    _ ≤ ‖centeredCharacterPsi t χ.primitiveCharacter‖ +
        ‖centeredCharacterPsi t χ - centeredCharacterPsi t χ.primitiveCharacter‖ := by
      have heq : centeredCharacterPsi t χ = centeredCharacterPsi t χ.primitiveCharacter +
          (centeredCharacterPsi t χ - centeredCharacterPsi t χ.primitiveCharacter) := by ring_nf
      conv_lhs => rw [heq]
      exact norm_add_le _ _
    _ ≤ characterMaxError T χ.primitiveCharacter + noncoprimeMangoldtMass T q :=
      add_le_add (norm_centeredCharacterPsi_le_max χ.primitiveCharacter htT)
        ((norm_centeredCharacterPsi_sub_primitive_le χ t).trans (noncoprimeMangoldtMass_mono q htT))

/-- Every character still appears once at its original modulus; replacing it
by its primitive character costs one copy of the excluded mass after averaging.-/
theorem progressionMaxError_le_primitiveCharacter_sum (T q : ℕ) (hq : 0 < q) :
    progressionMaxError T q ≤
      (∑ χ : DirichletCharacter ℂ q, characterMaxError T χ.primitiveCharacter) / Nat.totient q +
        noncoprimeMangoldtMass T q := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  apply (progressionMaxError_le_characterMaxError T q hq).trans
  calc
    _ ≤ (∑ χ : DirichletCharacter ℂ q,
        (characterMaxError T χ.primitiveCharacter + noncoprimeMangoldtMass T q)) / Nat.totient q :=
      div_le_div_of_nonneg_right (sum_le_sum fun χ _ => characterMaxError_le_primitive T χ) hφ.le
    _ = _ := by
      rw [sum_add_distrib]
      simp only [sum_const, card_univ, hcard, nsmul_eq_mul]
      field_simp

/-- A finite reduction of the exact progression maximum to primitive
character errors, with a completely explicit elementary replacement cost.-/
theorem sum_progressionMaxError_le_primitiveCharacter_sum (T Q : ℕ) (hT : 1 ≤ T) :
    (∑ q ∈ Icc 1 Q, progressionMaxError T q) ≤
      (∑ q ∈ Icc 1 Q,
        (∑ χ : DirichletCharacter ℂ q, characterMaxError T χ.primitiveCharacter) / Nat.totient q) +
        Q * (Real.log Q + 2 * Real.sqrt T * Real.log T) := by
  have hI : Icc 1 Q = Ioc 0 Q := by ext q; simp only [mem_Icc, mem_Ioc]; omega
  calc
    _ ≤ ∑ q ∈ Icc 1 Q,
        ((∑ χ : DirichletCharacter ℂ q, characterMaxError T χ.primitiveCharacter) / Nat.totient q +
          noncoprimeMangoldtMass T q) := by
      apply sum_le_sum
      intro q hq
      exact progressionMaxError_le_primitiveCharacter_sum T q (by have := (mem_Icc.mp hq).1; omega)
    _ = (∑ q ∈ Icc 1 Q,
        (∑ χ : DirichletCharacter ℂ q, characterMaxError T χ.primitiveCharacter) / Nat.totient q) +
        ∑ q ∈ Icc 1 Q, noncoprimeMangoldtMass T q := sum_add_distrib
    _ ≤ _ := by
      apply add_le_add le_rfl
      rw [hI]
      exact sum_noncoprimeMangoldtMass_le_uniform T Q hT (fun _ => T) (fun _ _ => le_rfl)

/-- At the exact BV endpoint and a suitable logarithmic modulus loss, the
primitive replacement error is absorbed into the requested error scale.-/
theorem eventually_sum_progressionMaxError_le_primitiveCharacter_sum
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 2) →
      (∑ q ∈ Icc 1 Q, progressionMaxError (2 * X + 2) q) ≤
        (∑ q ∈ Icc 1 Q,
          (∑ χ : DirichletCharacter ℂ q, characterMaxError (2 * X + 2) χ.primitiveCharacter) /
            Nat.totient q) + (X : ℝ) / (Real.log X) ^ A := by
  filter_upwards [eventually_characterExceptionBudget_le A hA] with X hX Q hQ
  have hfinite := sum_progressionMaxError_le_primitiveCharacter_sum (2 * X + 2) Q (by omega)
  apply hfinite.trans
  apply add_le_add le_rfl
  simpa only [characterExceptionBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hX Q hQ

end TwinPrime.Analytic
