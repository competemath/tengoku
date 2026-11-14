import Tengoku.Twinprime.TwinPrime.Analytic.CharacterVaughanTypeI
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterTrivialBounds
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterVaughanDyadic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform primitive-character bounds for Vaughan Type I

The exact factor sums and the proved primitive interval estimates give
pointwise budgets uniform in the endpoint. Their finite maxima therefore
have the same budgets, with no additional logarithmic loss.
-/

noncomputable section

open Finset Classical
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

theorem sum_norm_moebius_Ioc_le (U : ℕ) :
    (∑ d ∈ Ioc 0 U, ‖((μ d : ℝ) : ℂ)‖) ≤ (U : ℝ) := by
  calc
    _ ≤ ∑ _ ∈ Ioc 0 U, (1 : ℝ) := by
      apply sum_le_sum
      intro d _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    _ = _ := by simp

theorem sum_norm_vaughanCoefficient_Ioc_le (U V : ℕ) :
    (∑ d ∈ Ioc 0 (U * V), ‖(vaughanCoefficient U V d : ℂ)‖) ≤
      (U * V : ℕ) * Real.log (U * V : ℕ) := by
  calc
    _ ≤ ∑ _ ∈ Ioc 0 (U * V), Real.log (U * V : ℕ) := by
      apply sum_le_sum
      intro d hd
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_vaughanCoefficient_le_log U V d).trans (log_natCast_mono (mem_Ioc.mp hd).2)
    _ = _ := by simp

theorem norm_characterVaughanI1_le {q : ℕ} (hq : 1 < q)
    (U t T : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ht : t ≤ T) :
    ‖characterVaughanI1 U t χ‖ ≤
      2 * (U : ℝ) * Real.sqrt q * (1 + Real.log q) * Real.log T := by
  rw [characterVaughanI1_eq_factor_sum]
  have h := norm_sum_typeI_log_character_le_uniform hq χ hχ (Ioc 0 U)
    (fun d => ((μ d : ℝ) : ℂ)) T (fun d => t / d)
    (fun d _ => (Nat.div_le_self t d).trans ht)
  have hlogq := Real.log_natCast_nonneg q
  have hlogT := Real.log_natCast_nonneg T
  calc
    _ ≤ (2 * Real.sqrt q * (1 + Real.log q) * Real.log T) *
        ∑ d ∈ Ioc 0 U, ‖((μ d : ℝ) : ℂ)‖ := h
    _ ≤ (2 * Real.sqrt q * (1 + Real.log q) * Real.log T) * U :=
      mul_le_mul_of_nonneg_left (sum_norm_moebius_Ioc_le U) (by positivity)
    _ = _ := by ring

theorem norm_characterVaughanI2_le {q : ℕ} (hq : 1 < q)
    (U V t : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖characterVaughanI2 U V t χ‖ ≤
      ((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) * Real.sqrt q * (1 + Real.log q) := by
  rw [characterVaughanI2_eq_factor_sum]
  have hlogq := Real.log_natCast_nonneg q
  calc
    _ ≤ ∑ d ∈ Ioc 0 (U * V),
        ‖(vaughanCoefficient U V d : ℂ) * χ d * ∑ r ∈ Ioc 0 (t / d), χ r‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Ioc 0 (U * V), ‖(vaughanCoefficient U V d : ℂ)‖ *
        (Real.sqrt q * (1 + Real.log q)) := by
      apply sum_le_sum
      intro d _
      rw [norm_mul, norm_mul]
      exact mul_le_mul
        (mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _))
        (norm_sum_primitive_character_Ioc_le hq χ hχ (t / d))
        (norm_nonneg _) (norm_nonneg _)
    _ = (∑ d ∈ Ioc 0 (U * V), ‖(vaughanCoefficient U V d : ℂ)‖) *
        (Real.sqrt q * (1 + Real.log q)) := by rw [sum_mul]
    _ ≤ (((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ)) *
        (Real.sqrt q * (1 + Real.log q)) :=
      mul_le_mul_of_nonneg_right (sum_norm_vaughanCoefficient_Ioc_le U V) (by positivity)
    _ = _ := by ring

def characterVaughanI1Max {q : ℕ} (U T : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (Icc 0 T).sup' ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩
    (fun t => ‖characterVaughanI1 U t χ‖)

def characterVaughanI2Max {q : ℕ} (U V T : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (Icc 0 T).sup' ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩
    (fun t => ‖characterVaughanI2 U V t χ‖)

theorem norm_characterVaughanI1_le_max {q : ℕ} (U t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖characterVaughanI1 U t χ‖ ≤ characterVaughanI1Max U T χ :=
  Finset.le_sup' (f := fun t => ‖characterVaughanI1 U t χ‖) (mem_Icc.mpr ⟨Nat.zero_le t, ht⟩)

theorem norm_characterVaughanI2_le_max {q : ℕ} (U V t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖characterVaughanI2 U V t χ‖ ≤ characterVaughanI2Max U V T χ :=
  Finset.le_sup' (f := fun t => ‖characterVaughanI2 U V t χ‖) (mem_Icc.mpr ⟨Nat.zero_le t, ht⟩)

theorem characterVaughanI1Max_nonneg {q : ℕ} (U T : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ characterVaughanI1Max U T χ :=
  (norm_nonneg _).trans (norm_characterVaughanI1_le_max U 0 T χ (Nat.zero_le T))

theorem characterVaughanI2Max_nonneg {q : ℕ} (U V T : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ characterVaughanI2Max U V T χ :=
  (norm_nonneg _).trans (norm_characterVaughanI2_le_max U V 0 T χ (Nat.zero_le T))

theorem characterVaughanI1Max_le {q : ℕ} (hq : 1 < q)
    (U T : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    characterVaughanI1Max U T χ ≤
      2 * (U : ℝ) * Real.sqrt q * (1 + Real.log q) * Real.log T := by
  unfold characterVaughanI1Max
  apply Finset.sup'_le
  intro t ht
  exact norm_characterVaughanI1_le hq U t T χ hχ (mem_Icc.mp ht).2

theorem characterVaughanI2Max_le {q : ℕ} (hq : 1 < q)
    (U V T : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    characterVaughanI2Max U V T χ ≤
      ((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) * Real.sqrt q * (1 + Real.log q) := by
  unfold characterVaughanI2Max
  apply Finset.sup'_le
  intro t _
  exact norm_characterVaughanI2_le hq U V t χ hχ

/-- The full finite character maximum retains both Type I maxima, the low
von Mangoldt term, and the actual Type II maximum.-/
theorem characterPsiMax_le_vaughan (U V T : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    characterPsiMax T χ ≤ characterVaughanI1Max U T χ + characterVaughanI2Max U V T χ +
      (V : ℝ) * Real.log V + characterVaughanIIMax U V T χ := by
  unfold characterPsiMax
  apply Finset.sup'_le
  intro t ht
  have htT := (mem_Icc.mp ht).2
  rw [characterPsi_eq_vaughan_types U V t χ]
  calc
    _ ≤ ‖characterVaughanI1 U t χ - characterVaughanI2 U V t χ +
        characterPsi (min t V) χ‖ + ‖characterVaughanII U V t χ‖ := norm_add_le _ _
    _ ≤ (‖characterVaughanI1 U t χ - characterVaughanI2 U V t χ‖ +
        ‖characterPsi (min t V) χ‖) + ‖characterVaughanII U V t χ‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖characterVaughanI1 U t χ‖ + ‖characterVaughanI2 U V t χ‖) +
        ‖characterPsi (min t V) χ‖) + ‖characterVaughanII U V t χ‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ _ := add_le_add
      (add_le_add (add_le_add (norm_characterVaughanI1_le_max U t T χ htT)
        (norm_characterVaughanI2_le_max U V t T χ htT)) (norm_characterPsi_min_le V t χ))
      (norm_characterVaughanII_le_max U V t T χ htT)

end TwinPrime.Analytic
