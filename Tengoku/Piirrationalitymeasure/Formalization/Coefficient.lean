import Tengoku.Piirrationalitymeasure.Formalization.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Positive generating-function data for the coefficient estimate in Section 4.
-/

namespace PiIrrationality

noncomputable def SReal (z : ℝ) : ℝ :=
  (1 + z) ^ 3714 * (PReal z) ^ 3714 / (1 - z) ^ 7430

def Pcoeff (k : Fin 5) : ℕ :=
  match k.1 with
  | 0 => 2
  | 1 => 6
  | 2 => 9
  | 3 => 6
  | _ => 2

theorem Pcoeff_pos (k : Fin 5) : 0 < Pcoeff k := by
  fin_cases k <;> norm_num [Pcoeff]

theorem P_support_contains_zero : Pcoeff 0 ≠ 0 := by
  norm_num [Pcoeff]

theorem P_support_contains_one : Pcoeff 1 ≠ 0 := by
  norm_num [Pcoeff]

theorem SReal_pos {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 0 < SReal z := by
  unfold SReal
  have hplus : 0 < 1 + z := by linarith
  have hP : 0 < PReal z := PReal_strictPositive z hz0
  have hminus : 0 < 1 - z := by linarith
  have hnum : 0 < (1 + z) ^ 3714 * (PReal z) ^ 3714 :=
    mul_pos (pow_pos hplus _) (pow_pos hP _)
  have hden : 0 < (1 - z) ^ 7430 := pow_pos hminus _
  exact div_pos hnum hden

theorem SReal_ne_zero {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : SReal z ≠ 0 :=
  ne_of_gt (SReal_pos hz0 hz1)

end PiIrrationality
