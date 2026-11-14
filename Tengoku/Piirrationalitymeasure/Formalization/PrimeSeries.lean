import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.PrimeSaving

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Real-valued convergence certificates for the periodic endpoint series in
Section 3.2.
-/

namespace PiIrrationality

noncomputable def periodicSummandReal (ell r : ℝ) (q : ℕ) : ℝ :=
  (r - ell) / (((q : ℝ) + ell) * ((q : ℝ) + r))

theorem periodicSummandReal_nonneg {ell r : ℝ}
    (hℓ : 0 < ell) (hord : ell < r) (q : ℕ) :
    0 ≤ periodicSummandReal ell r q := by
  unfold periodicSummandReal
  have hq : 0 ≤ (q : ℝ) := by positivity
  apply div_nonneg (le_of_lt (sub_pos.mpr hord))
  exact le_of_lt (mul_pos (by linarith) (by linarith))

theorem periodicSummandReal_shift_le_inv_sq {ell r : ℝ}
    (hℓ : 0 < ell) (hord : ell < r) (hr : r ≤ 1) (q : ℕ) :
    periodicSummandReal ell r (q + 1) ≤
      1 / ((q + 1 : ℕ) : ℝ) ^ 2 := by
  have hxpos : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
  have hxone : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q))
  have hden : 0 < ((((q + 1 : ℕ) : ℝ) + ell) *
      (((q + 1 : ℕ) : ℝ) + r)) := by
    exact mul_pos (by linarith) (by linarith)
  have hx2 : 0 < ((q + 1 : ℕ) : ℝ) ^ 2 := sq_pos_of_pos hxpos
  apply (div_le_div_iff₀ hden hx2).2
  have hnum : r - ell ≤ 1 := by linarith
  have hprod : ((q + 1 : ℕ) : ℝ) ^ 2 ≤
      (((q + 1 : ℕ) : ℝ) + ell) * (((q + 1 : ℕ) : ℝ) + r) := by
    nlinarith [mul_pos hℓ (by linarith : 0 < r)]
  calc
    (r - ell) * ((q + 1 : ℕ) : ℝ) ^ 2 ≤
        1 * ((q + 1 : ℕ) : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ 1 * ((((q + 1 : ℕ) : ℝ) + ell) *
        (((q + 1 : ℕ) : ℝ) + r)) := by
      exact mul_le_mul_of_nonneg_left hprod (by norm_num)

theorem periodicSummandReal_antitone {ell r : ℝ}
    (hℓ : 0 < ell) (hord : ell < r) :
    Antitone (fun q : ℕ => periodicSummandReal ell r q) := by
  intro m n hmn
  unfold periodicSummandReal
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hnum : 0 ≤ r - ell := sub_nonneg.mpr hord.le
  have hdenm : 0 < ((m : ℝ) + ell) * ((m : ℝ) + r) := by
    exact mul_pos (by linarith) (by linarith)
  have hdenord : ((m : ℝ) + ell) * ((m : ℝ) + r) ≤
      ((n : ℝ) + ell) * ((n : ℝ) + r) := by
    calc
      ((m : ℝ) + ell) * ((m : ℝ) + r) ≤
          ((n : ℝ) + ell) * ((m : ℝ) + r) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ ((n : ℝ) + ell) * ((n : ℝ) + r) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  exact div_le_div_of_nonneg_left hnum hdenm hdenord

theorem periodicSummandReal_summable {ell r : ℝ}
    (hℓ : 0 < ell) (hord : ell < r) (hr : r ≤ 1) :
    Summable (fun q => periodicSummandReal ell r q) := by
  have hp : Summable (fun q : ℕ => 1 / (q : ℝ) ^ 2) := by
    exact Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp_shift : Summable (fun q : ℕ =>
      1 / ((q + 1 : ℕ) : ℝ) ^ 2) := by
    have hs := (summable_nat_add_iff (f := fun q : ℕ => 1 / (q : ℝ) ^ 2) 1).2 hp
    simpa [Nat.cast_add] using hs
  have hs : Summable (fun q : ℕ => periodicSummandReal ell r (q + 1)) := by
    apply Summable.of_nonneg_of_le
    · intro q
      exact periodicSummandReal_nonneg hℓ hord (q + 1)
    · intro q
      exact periodicSummandReal_shift_le_inv_sq hℓ hord hr q
    · exact hp_shift
  exact (summable_nat_add_iff (f := fun q : ℕ => periodicSummandReal ell r q) 1).mp hs

end PiIrrationality
