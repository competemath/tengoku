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

/--
@isnad1 id=lt.0h1v.s4.ea8670d87490 from=translated src=- shape=dfc00b87 vocab=995870b0
-/
theorem Pcoeff_pos (k : Fin 5) : 0 < Pcoeff k := by
  fin_cases k <;> norm_num [Pcoeff]

/--
@isnad1 id=ne.0h0v.s4.6c5b654910fa from=translated src=- shape=3ffd5d8e vocab=23d7e730
-/
theorem P_support_contains_zero : Pcoeff 0 ≠ 0 := by
  norm_num [Pcoeff]

/--
@isnad1 id=ne.0h0v.s4.925d456fcb5b from=translated src=- shape=3ffd5d8e vocab=23d7e730
-/
theorem P_support_contains_one : Pcoeff 1 ≠ 0 := by
  norm_num [Pcoeff]

/--
@isnad1 id=lt.2h1v.s5.44a8ab146898 from=translated src=- shape=536e06c9 vocab=f6d2fd30
-/
theorem SReal_pos {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 0 < SReal z := by
  unfold SReal
  have hplus : 0 < 1 + z := by linarith
  have hP : 0 < PReal z := PReal_strictPositive z hz0
  have hminus : 0 < 1 - z := by linarith
  have hnum : 0 < (1 + z) ^ 3714 * (PReal z) ^ 3714 :=
    mul_pos (pow_pos hplus _) (pow_pos hP _)
  have hden : 0 < (1 - z) ^ 7430 := pow_pos hminus _
  exact div_pos hnum hden

/--
@isnad1 id=ne.2h1v.s5.7585eb796648 from=translated src=- shape=8bbe90a8 vocab=f6d2fd30
-/
theorem SReal_ne_zero {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : SReal z ≠ 0 :=
  ne_of_gt (SReal_pos hz0 hz1)

end PiIrrationality
