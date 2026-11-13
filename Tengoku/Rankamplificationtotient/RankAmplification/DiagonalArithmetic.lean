import Tengoku.Rankamplificationtotient.RankAmplification.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Arithmetic of the diagonal coefficients Exact gcd and affine identities behind the Graham--Holt--Pomerance diagonal parametrization. -/

namespace RankAmplification

theorem diagonalGCD_dvd_left (h j : ℕ) : diagonalGCD h j ∣ j := by
  exact Nat.gcd_dvd_left j (j + h)

theorem diagonalGCD_dvd_right (h j : ℕ) : diagonalGCD h j ∣ j + h := by
  exact Nat.gcd_dvd_right j (j + h)

theorem diagonalB_mul_diagonalGCD (h j : ℕ) :
    diagonalB h j * diagonalGCD h j = j := by
  exact Nat.div_mul_cancel (diagonalGCD_dvd_left h j)

theorem diagonalGCD_mul_diagonalB (h j : ℕ) :
    diagonalGCD h j * diagonalB h j = j := by
  rw [mul_comm]
  exact diagonalB_mul_diagonalGCD h j

theorem diagonalA_mul_diagonalGCD (h j : ℕ) :
    diagonalA h j * diagonalGCD h j = j + h := by
  exact Nat.div_mul_cancel (diagonalGCD_dvd_right h j)

theorem diagonalGCD_mul_diagonalA (h j : ℕ) :
    diagonalGCD h j * diagonalA h j = j + h := by
  rw [mul_comm]
  exact diagonalA_mul_diagonalGCD h j

theorem diagonal_cross_mul (h j : ℕ) :
    (j + h) * diagonalB h j = j * diagonalA h j := by
  calc
    (j + h) * diagonalB h j =
        (diagonalGCD h j * diagonalA h j) * diagonalB h j := by
          rw [diagonalGCD_mul_diagonalA]
    _ = (diagonalGCD h j * diagonalB h j) * diagonalA h j := by
          ac_rfl
    _ = j * diagonalA h j := by rw [diagonalGCD_mul_diagonalB]

theorem diagonalB_pos {h j : ℕ} (hj : 0 < j) : 0 < diagonalB h j := by
  apply Nat.div_pos
  · exact Nat.gcd_le_left (j + h) hj
  · exact Nat.gcd_pos_of_pos_left (j + h) hj

theorem diagonalA_pos {h j : ℕ} (hj : 0 < j) : 0 < diagonalA h j := by
  apply Nat.div_pos
  · exact Nat.gcd_le_right j (by omega)
  · exact Nat.gcd_pos_of_pos_left (j + h) hj

end RankAmplification
