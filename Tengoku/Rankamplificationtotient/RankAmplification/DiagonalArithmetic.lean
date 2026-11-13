import Tengoku.Rankamplificationtotient.RankAmplification.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Arithmetic of the diagonal coefficients Exact gcd and affine identities behind the Graham--Holt--Pomerance diagonal parametrization. -/

namespace RankAmplification

/--
@isnad1 id=dvd.0h2v.s3.27a49eb18e30 from=translated src=- shape=bf83e09e vocab=973d0f4c
-/
theorem diagonalGCD_dvd_left (h j : ℕ) : diagonalGCD h j ∣ j := by
  exact Nat.gcd_dvd_left j (j + h)

/--
@isnad1 id=dvd.0h2v.s4.ed8a9d6af90e from=translated src=- shape=8cea4b4e vocab=1d844867
-/
theorem diagonalGCD_dvd_right (h j : ℕ) : diagonalGCD h j ∣ j + h := by
  exact Nat.gcd_dvd_right j (j + h)

/--
@isnad1 id=eq.0h2v.s4.3551d70fc9c3 from=translated src=- shape=5e050e43 vocab=6ab35c48
-/
theorem diagonalB_mul_diagonalGCD (h j : ℕ) :
    diagonalB h j * diagonalGCD h j = j := by
  exact Nat.div_mul_cancel (diagonalGCD_dvd_left h j)

/--
@isnad1 id=eq.0h2v.s4.8a1d1de98a58 from=translated src=- shape=5e050e43 vocab=6ab35c48
-/
theorem diagonalGCD_mul_diagonalB (h j : ℕ) :
    diagonalGCD h j * diagonalB h j = j := by
  rw [mul_comm]
  exact diagonalB_mul_diagonalGCD h j

/--
@isnad1 id=eq.0h2v.s4.1e52caebbd20 from=translated src=- shape=dfe80031 vocab=a17097f5
-/
theorem diagonalA_mul_diagonalGCD (h j : ℕ) :
    diagonalA h j * diagonalGCD h j = j + h := by
  exact Nat.div_mul_cancel (diagonalGCD_dvd_right h j)

/--
@isnad1 id=eq.0h2v.s4.b2583c5a5ebd from=translated src=- shape=dfe80031 vocab=a17097f5
-/
theorem diagonalGCD_mul_diagonalA (h j : ℕ) :
    diagonalGCD h j * diagonalA h j = j + h := by
  rw [mul_comm]
  exact diagonalA_mul_diagonalGCD h j

/--
@isnad1 id=eq.0h2v.s5.c13ca00e5563 from=translated src=- shape=5dfa3765 vocab=9932722d
-/
theorem diagonal_cross_mul (h j : ℕ) :
    (j + h) * diagonalB h j = j * diagonalA h j := by
  calc
    (j + h) * diagonalB h j =
        (diagonalGCD h j * diagonalA h j) * diagonalB h j := by
          rw [diagonalGCD_mul_diagonalA]
    _ = (diagonalGCD h j * diagonalB h j) * diagonalA h j := by
          ac_rfl
    _ = j * diagonalA h j := by rw [diagonalGCD_mul_diagonalB]

/--
@isnad1 id=lt.1h2v.s4.a0f9453e3ddc from=translated src=- shape=61bdc3e7 vocab=485b7cfc
-/
theorem diagonalB_pos {h j : ℕ} (hj : 0 < j) : 0 < diagonalB h j := by
  apply Nat.div_pos
  · exact Nat.gcd_le_left (j + h) hj
  · exact Nat.gcd_pos_of_pos_left (j + h) hj

/--
@isnad1 id=lt.1h2v.s4.07d4518b07b3 from=translated src=- shape=61bdc3e7 vocab=3fee6977
-/
theorem diagonalA_pos {h j : ℕ} (hj : 0 < j) : 0 < diagonalA h j := by
  apply Nat.div_pos
  · exact Nat.gcd_le_right j (by omega)
  · exact Nat.gcd_pos_of_pos_left (j + h) hj

end RankAmplification
