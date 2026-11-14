import Tengoku.Twinprime.TwinPrime.Analytic.CharacterMaximal
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterLogInterval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary bounds for uncentered character sums

The finite uncentered maximum has the elementary budget `T log T`.
This includes the low Vaughan term and modulus one. For a nonprincipal
character it agrees exactly with the existing centered maximum.
-/

noncomputable section

open Finset ArithmeticFunction Classical

namespace TwinPrime.Analytic

theorem norm_characterPsi_le {q : ℕ} (t : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖characterPsi t χ‖ ≤ (t : ℝ) * Real.log (t : ℝ) := by
  unfold characterPsi
  calc
    _ ≤ ∑ n ∈ Ioc 0 t, ‖(vonMangoldt n : ℂ) * χ n‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ Ioc 0 t, Real.log (t : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact (mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)).trans
        (vonMangoldt_le_log.trans (log_natCast_mono (mem_Ioc.mp hn).2))
    _ = _ := by simp

theorem norm_characterPsi_le_uniform {q : ℕ} (t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖characterPsi t χ‖ ≤ (T : ℝ) * Real.log (T : ℝ) := by
  apply (norm_characterPsi_le t χ).trans
  exact mul_le_mul (by exact_mod_cast ht) (log_natCast_mono ht)
    (Real.log_natCast_nonneg t) (Nat.cast_nonneg T)

theorem norm_characterPsi_min_le {q : ℕ} (V t : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖characterPsi (min t V) χ‖ ≤ (V : ℝ) * Real.log (V : ℝ) :=
  norm_characterPsi_le_uniform (min t V) V χ (min_le_right _ _)

/-- The uncentered finite character maximum, including endpoint zero.-/
def characterPsiMax {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (Icc 0 T).sup' ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩
    (fun t => ‖characterPsi t χ‖)

theorem norm_characterPsi_le_max {q : ℕ} (t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖characterPsi t χ‖ ≤ characterPsiMax T χ :=
  Finset.le_sup' (f := fun t => ‖characterPsi t χ‖) (mem_Icc.mpr ⟨Nat.zero_le t, ht⟩)

theorem characterPsiMax_nonneg {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ characterPsiMax T χ :=
  (norm_nonneg _).trans (norm_characterPsi_le_max 0 T χ (Nat.zero_le T))

theorem characterPsiMax_le {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) :
    characterPsiMax T χ ≤ (T : ℝ) * Real.log (T : ℝ) := by
  unfold characterPsiMax
  apply Finset.sup'_le
  intro t ht
  exact norm_characterPsi_le_uniform t T χ (mem_Icc.mp ht).2

theorem characterMaxError_eq_characterPsiMax_of_ne_one {q : ℕ}
    (T : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    characterMaxError T χ = characterPsiMax T χ := by
  have hI : range (T + 1) = Icc 0 T := by
    ext t
    simp only [mem_range, mem_Icc]
    omega
  unfold characterMaxError characterPsiMax
  simp only [centeredCharacterPsi, ite_eq_right hχ, sub_zero]
  simp only [hI]

theorem primitive_characterMaxError_eq_characterPsiMax {q : ℕ}
    (hq : 1 < q) (T : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    characterMaxError T χ = characterPsiMax T χ :=
  characterMaxError_eq_characterPsiMax_of_ne_one T χ (primitive_character_ne_one hq χ hχ)

end TwinPrime.Analytic
