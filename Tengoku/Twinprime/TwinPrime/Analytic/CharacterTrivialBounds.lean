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

/--
@isnad1 id=le.0h3v.s5.bf0cce418e1f from=translated src=- shape=3a28621c vocab=df407631
-/
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

/--
@isnad1 id=le.1h4v.s5.0cba907644e4 from=translated src=- shape=98844958 vocab=df407631
-/
theorem norm_characterPsi_le_uniform {q : ℕ} (t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖characterPsi t χ‖ ≤ (T : ℝ) * Real.log (T : ℝ) := by
  apply (norm_characterPsi_le t χ).trans
  exact mul_le_mul (by exact_mod_cast ht) (log_natCast_mono ht)
    (Real.log_natCast_nonneg t) (Nat.cast_nonneg T)

/--
@isnad1 id=le.0h4v.s5.ae0062dedf05 from=translated src=- shape=4c17585f vocab=aaee5a35
-/
theorem norm_characterPsi_min_le {q : ℕ} (V t : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖characterPsi (min t V) χ‖ ≤ (V : ℝ) * Real.log (V : ℝ) :=
  norm_characterPsi_le_uniform (min t V) V χ (min_le_right _ _)

/-- The uncentered finite character maximum, including endpoint zero.-/
def characterPsiMax {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (Icc 0 T).sup' ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩
    (fun t => ‖characterPsi t χ‖)

/--
@isnad1 id=le.1h4v.s5.57cb4f137ba2 from=translated src=- shape=0519443a vocab=4d13a2d4
-/
theorem norm_characterPsi_le_max {q : ℕ} (t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖characterPsi t χ‖ ≤ characterPsiMax T χ :=
  Finset.le_sup' (f := fun t => ‖characterPsi t χ‖) (mem_Icc.mpr ⟨Nat.zero_le t, ht⟩)

/--
@isnad1 id=le.0h3v.s4.86bdd83a0674 from=translated src=- shape=a11b2b73 vocab=ba713c74
-/
theorem characterPsiMax_nonneg {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ characterPsiMax T χ :=
  (norm_nonneg _).trans (norm_characterPsi_le_max 0 T χ (Nat.zero_le T))

/--
@isnad1 id=le.0h3v.s5.db71e2f2c11c from=translated src=- shape=f372dcb9 vocab=fedecd77
-/
theorem characterPsiMax_le {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) :
    characterPsiMax T χ ≤ (T : ℝ) * Real.log (T : ℝ) := by
  unfold characterPsiMax
  apply Finset.sup'_le
  intro t ht
  exact norm_characterPsi_le_uniform t T χ (mem_Icc.mp ht).2

/--
@isnad1 id=eq.1h3v.s6.81ac645de4f3 from=translated src=- shape=59b76396 vocab=7370f5dc
-/
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

/--
@isnad1 id=eq.2h3v.s5.beb98ead3ffe from=translated src=- shape=42404672 vocab=ee166904
-/
theorem primitive_characterMaxError_eq_characterPsiMax {q : ℕ}
    (hq : 1 < q) (T : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    characterMaxError T χ = characterPsiMax T χ :=
  characterMaxError_eq_characterPsiMax_of_ne_one T χ (primitive_character_ne_one hq χ hχ)

end TwinPrime.Analytic
