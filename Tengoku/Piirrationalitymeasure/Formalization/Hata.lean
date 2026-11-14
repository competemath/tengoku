import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace PiIrrationality

/- The integer-linear-form notation used in the Hata step. -/
def linearForm (theta : ℝ) (U V : ℤ) : ℝ := (U : ℝ) + (V : ℝ) * theta

def hataDelta (theta : ℝ) (p : ℤ) (q : ℕ) : ℝ := (q : ℝ) * theta - (p : ℝ)

def hataInteger (U V : ℤ) (p : ℤ) (q : ℕ) : ℤ :=
  (q : ℤ) * U + p * V

theorem hata_determinant_identity (theta : ℝ) (U V p : ℤ) (q : ℕ) :
    (q : ℝ) * linearForm theta U V =
      (hataInteger U V p q : ℝ) + (V : ℝ) * hataDelta theta p q := by
  simp [linearForm, hataInteger, hataDelta]
  ring

theorem hata_delta_factorization (theta : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) :
    hataDelta theta p q = (q : ℝ) * (theta - (p : ℝ) / (q : ℝ)) := by
  simp [hataDelta]
  field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hq)]

theorem hata_delta_abs_factorization (theta : ℝ) (p : ℤ) (q : ℕ)
    (hq : 0 < q) :
    |hataDelta theta p q| = (q : ℝ) * |theta - (p : ℝ) / (q : ℝ)| := by
  rw [hata_delta_factorization theta p q hq, abs_mul,
    abs_of_pos (by exact_mod_cast hq)]

theorem linearForm_ne_zero_of_irrational {theta : ℝ} (hθ : Irrational theta)
    {U V : ℤ} (hV : V ≠ 0) : linearForm theta U V ≠ 0 := by
  intro hzero
  apply hθ
  let r : ℚ := (-U : ℚ) / (V : ℚ)
  refine ⟨r, ?_⟩
  have hVr : (V : ℝ) ≠ 0 := by exact_mod_cast hV
  dsimp [linearForm] at hzero
  dsimp [r]
  rw [Rat.cast_div, Rat.cast_neg, Rat.cast_intCast, Rat.cast_intCast]
  field_simp [hVr] at hzero ⊢
  linarith

theorem pi_linearForm_ne_zero {U V : ℤ} (hV : V ≠ 0) :
    linearForm Real.pi U V ≠ 0 :=
  linearForm_ne_zero_of_irrational irrational_pi hV

theorem hata_delta_lower_of_integer_ne_zero (theta : ℝ) (U V p : ℤ) (q : ℕ)
    (hq : 0 < q) (hV : V ≠ 0)
    (hA : hataInteger U V p q ≠ 0)
    (hsmall : |(q : ℝ) * linearForm theta U V| < (1 : ℝ) / 2) :
    |hataDelta theta p q| > (1 : ℝ) / (2 * |(V : ℝ)|) := by
  have hVreal : (V : ℝ) ≠ 0 := by exact_mod_cast hV
  have hAabs : (1 : ℝ) ≤ |(hataInteger U V p q : ℝ)| := by
    have hnat : 1 ≤ (hataInteger U V p q).natAbs := by
      exact Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr hA)
    have hnat' : (1 : ℝ) ≤ ((hataInteger U V p q).natAbs : ℝ) := by
      exact_mod_cast hnat
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact hnat'
  have hdet := hata_determinant_identity theta U V p q
  have htriangle :
      |(hataInteger U V p q : ℝ)| ≤
        |(q : ℝ) * linearForm theta U V| + |(V : ℝ) * hataDelta theta p q| := by
    calc
      |(hataInteger U V p q : ℝ)| =
          |(q : ℝ) * linearForm theta U V - (V : ℝ) * hataDelta theta p q| := by
            rw [hdet]
            congr 1
            ring
      _ ≤ |(q : ℝ) * linearForm theta U V| + |(V : ℝ) * hataDelta theta p q| := by
        exact abs_sub _ _
  have hprod : (1 : ℝ) / 2 < |(V : ℝ) * hataDelta theta p q| := by
    linarith [hAabs, htriangle, hsmall]
  rw [abs_mul] at hprod
  have hVpos : 0 < |(V : ℝ)| := abs_pos.mpr hVreal
  apply (div_lt_iff₀ (mul_pos (by norm_num) hVpos)).mpr
  nlinarith [hprod]

theorem hata_delta_eq_of_integer_zero (theta : ℝ) (U V p : ℤ) (q : ℕ)
    (hV : V ≠ 0) (hA : hataInteger U V p q = 0) :
    hataDelta theta p q =
      (q : ℝ) * linearForm theta U V / (V : ℝ) := by
  have hVreal : (V : ℝ) ≠ 0 := by exact_mod_cast hV
  have hdet := hata_determinant_identity theta U V p q
  rw [hA] at hdet
  field_simp [hVreal]
  simpa [mul_comm] using hdet.symm

theorem hata_delta_abs_eq_of_integer_zero (theta : ℝ) (U V p : ℤ) (q : ℕ)
    (hV : V ≠ 0) (hA : hataInteger U V p q = 0) :
    |hataDelta theta p q| =
      |(q : ℝ) * linearForm theta U V| / |(V : ℝ)| := by
  rw [hata_delta_eq_of_integer_zero theta U V p q hV hA, abs_div]

theorem hata_delta_dichotomy (theta : ℝ) (U V p : ℤ) (q : ℕ)
    (hq : 0 < q) (hV : V ≠ 0)
    (hsmall : |(q : ℝ) * linearForm theta U V| < (1 : ℝ) / 2) :
    (hataInteger U V p q ≠ 0 ∧
        |hataDelta theta p q| > (1 : ℝ) / (2 * |(V : ℝ)|)) ∨
      (hataInteger U V p q = 0 ∧
        |hataDelta theta p q| =
          |(q : ℝ) * linearForm theta U V| / |(V : ℝ)|) := by
  by_cases hA : hataInteger U V p q ≠ 0
  · left
    exact ⟨hA, hata_delta_lower_of_integer_ne_zero theta U V p q hq hV hA hsmall⟩
  · right
    have hA0 : hataInteger U V p q = 0 := by exact not_ne_iff.mp hA
    exact ⟨hA0, hata_delta_abs_eq_of_integer_zero theta U V p q hV hA0⟩

end PiIrrationality
