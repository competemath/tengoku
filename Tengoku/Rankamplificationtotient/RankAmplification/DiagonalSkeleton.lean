import Tengoku.Rankamplificationtotient.RankAmplification.SmallCofactor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Diagonal provider skeletons This module proves the converse direction of Proposition 9.4: a provider skeleton whose normalized affine slope vanishes is exactly one of the Graham--Holt--Pomerance diagonal prime pairs. -/

namespace RankAmplification

/-- The paper's diagonal condition `m₁a = m₂b` for a provider skeleton.-/
def LargePrimeSkeleton.IsDiagonal {h n p : ℕ} (s : LargePrimeSkeleton h n p) : Prop :=
  s.m1 * normalizedA s.m1 s.m2 = s.m2 * normalizedB s.m1 s.m2

/-- Two positive coprime pairs representing the same rational number agree coordinatewise.-/
theorem coprime_pair_eq_of_cross_mul {a b c d : ℕ} (ha : 0 < a)
    (hab : a.Coprime b) (hcd : c.Coprime d) (hcross : a * d = c * b) :
    a = c ∧ b = d := by
  have hac : a ∣ c := by
    apply hab.dvd_of_dvd_mul_right
    exact ⟨d, hcross.symm⟩
  have hca : c ∣ a := by
    apply hcd.dvd_of_dvd_mul_right
    exact ⟨b, hcross⟩
  have hacEq : a = c := Nat.dvd_antisymm hac hca
  subst c
  have hbd : d = b := Nat.mul_left_cancel ha hcross
  exact ⟨rfl, hbd.symm⟩

/-- The coefficients `(A_j,B_j)` form the reduced ratio `(j+h):j`.-/
theorem diagonalA_coprime_diagonalB {h j : ℕ} (hj : 0 < j) :
    (diagonalA h j).Coprime (diagonalB h j) := by
  have hg : 0 < Nat.gcd (j + h) j := Nat.gcd_pos_of_pos_right _ hj
  simpa only [diagonalA, diagonalB, diagonalGCD, Nat.gcd_comm] using
    (Nat.coprime_div_gcd_div_gcd hg)

theorem LargePrimeSkeleton.m2_eq_m1_add_h_of_diagonal {h n p : ℕ}
    (s : LargePrimeSkeleton h n p) (hdiag : s.IsDiagonal) :
    s.m2 = s.m1 + h := by
  obtain ⟨c, _hc, hk₁, hk₂⟩ := s.exists_pos_normalized_common_multiplier
  have hshift := s.normalized_shift_equation hk₁ hk₂
  have hexpanded :
      (s.m1 * normalizedA s.m1 s.m2) * (c * p) + (s.m1 + h) =
        (s.m2 * normalizedB s.m1 s.m2) * (c * p) + s.m2 := by
    calc
      (s.m1 * normalizedA s.m1 s.m2) * (c * p) + (s.m1 + h) =
          s.m1 * (normalizedA s.m1 s.m2 * (c * p) + 1) + h := by ring
      _ = s.m2 * (normalizedB s.m1 s.m2 * (c * p) + 1) := hshift
      _ = (s.m2 * normalizedB s.m1 s.m2) * (c * p) + s.m2 := by ring
  rw [hdiag] at hexpanded
  exact (Nat.add_left_cancel hexpanded).symm

theorem LargePrimeSkeleton.primeSupport_eq_of_diagonal {h n p : ℕ}
    (s : LargePrimeSkeleton h n p) (hdiag : s.IsDiagonal) :
    primeSupport s.m1 = primeSupport s.m2 := by
  have hcross := totient_cross_eq_of_normalized_diagonal hdiag
  exact primeSupport_eq_of_totient_cross_eq s.m1_pos.ne' s.m2_pos.ne' hcross

theorem LargePrimeSkeleton.sameSupportIndex_of_diagonal {h n p : ℕ}
    (s : LargePrimeSkeleton h n p) (hdiag : s.IsDiagonal) :
    IsSameSupportIndex h s.m1 := by
  refine ⟨s.m1_pos, ?_⟩
  rw [← s.m2_eq_m1_add_h_of_diagonal hdiag]
  exact s.primeSupport_eq_of_diagonal hdiag

/-- On a diagonal skeleton, the totient-normalized coefficients are exactly the geometric coefficients `A_j,B_j`.-/
theorem LargePrimeSkeleton.normalized_eq_diagonal_coefficients {h n p : ℕ}
    (s : LargePrimeSkeleton h n p) (hdiag : s.IsDiagonal) :
    normalizedA s.m1 s.m2 = diagonalA h s.m1 ∧
      normalizedB s.m1 s.m2 = diagonalB h s.m1 := by
  have hm₂ : s.m2 = s.m1 + h := s.m2_eq_m1_add_h_of_diagonal hdiag
  have hg : 0 < diagonalGCD h s.m1 := by
    exact Nat.gcd_pos_of_pos_left _ s.m1_pos
  have hm₁factor : s.m1 = diagonalB h s.m1 * diagonalGCD h s.m1 := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left s.m1 (s.m1 + h))).symm
  have hm₂factor : s.m1 + h = diagonalA h s.m1 * diagonalGCD h s.m1 := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right s.m1 (s.m1 + h))).symm
  have hcross :
      normalizedA s.m1 s.m2 * diagonalB h s.m1 =
        diagonalA h s.m1 * normalizedB s.m1 s.m2 := by
    apply Nat.mul_right_cancel hg
    calc
      (normalizedA s.m1 s.m2 * diagonalB h s.m1) * diagonalGCD h s.m1 =
          (diagonalB h s.m1 * diagonalGCD h s.m1) *
            normalizedA s.m1 s.m2 := by ac_rfl
      _ = s.m1 * normalizedA s.m1 s.m2 :=
        congrArg (fun t ↦ t * normalizedA s.m1 s.m2) hm₁factor.symm
      _ = s.m2 * normalizedB s.m1 s.m2 := hdiag
      _ = (s.m1 + h) * normalizedB s.m1 s.m2 :=
        congrArg (fun t ↦ t * normalizedB s.m1 s.m2) hm₂
      _ = (diagonalA h s.m1 * diagonalGCD h s.m1) *
          normalizedB s.m1 s.m2 :=
        congrArg (fun t ↦ t * normalizedB s.m1 s.m2) hm₂factor
      _ = (diagonalA h s.m1 * normalizedB s.m1 s.m2) *
          diagonalGCD h s.m1 := by ac_rfl
  have hnormCoprime := normalizedA_coprime_normalizedB s.m1_pos s.m2_pos
  have hdiagCoprime := diagonalA_coprime_diagonalB (h := h) s.m1_pos
  have hnormPos : 0 < normalizedA s.m1 s.m2 := by
    exact Nat.div_pos (Nat.gcd_le_right _ (Nat.totient_pos.mpr s.m2_pos))
      (Nat.gcd_pos_of_pos_left _ (Nat.totient_pos.mpr s.m1_pos))
  exact coprime_pair_eq_of_cross_mul hnormPos hnormCoprime hdiagCoprime hcross

/-- A diagonal skeleton yields the exact affine prime-pair representation, including any supplied largest-prime cutoff on its common totient.-/
theorem LargePrimeSkeleton.exists_diagonalRepresentation {h n p Y : ℕ}
    (s : LargePrimeSkeleton h n p) (hp : p.Prime) (hdiag : s.IsDiagonal)
    (hcut : Y < largestPrimeFactor n.totient) :
    ∃ r : ℕ, IsDiagonalRepresentation h Y n s.m1 r := by
  obtain ⟨c, hc, hk₁, hk₂⟩ := s.exists_pos_normalized_common_multiplier
  obtain ⟨ha, hb⟩ := s.normalized_eq_diagonal_coefficients hdiag
  let r := c * p
  have hr : 1 ≤ r := Nat.mul_pos hc hp.pos
  have hq₁ : s.q1 = diagonalA h s.m1 * r + 1 := by
    rw [s.q1_eq, hk₁, ha]
    simp only [r]
    ring
  have hq₂ : s.q2 = diagonalB h s.m1 * r + 1 := by
    rw [s.q2_eq, hk₂, hb]
    simp only [r]
    ring
  have hn : n = s.m1 * (diagonalA h s.m1 * r + 1) := by
    calc
      n = s.m1 * s.q1 := s.n_eq
      _ = s.m1 * (diagonalA h s.m1 * r + 1) :=
        congrArg (fun q ↦ s.m1 * q) hq₁
  have hm₂ : s.m2 = s.m1 + h := s.m2_eq_m1_add_h_of_diagonal hdiag
  have hnshift : n + h = (s.m1 + h) * (diagonalB h s.m1 * r + 1) := by
    calc
      n + h = s.m2 * s.q2 := s.shifted_eq
      _ = s.m2 * (diagonalB h s.m1 * r + 1) :=
        congrArg (fun q ↦ s.m2 * q) hq₂
      _ = (s.m1 + h) * (diagonalB h s.m1 * r + 1) :=
        congrArg (fun m ↦ m * (diagonalB h s.m1 * r + 1)) hm₂
  have hprimeA : Nat.Prime (diagonalA h s.m1 * r + 1) := by rw [← hq₁]; exact s.q1_prime
  have hprimeB : Nat.Prime (diagonalB h s.m1 * r + 1) := by rw [← hq₂]; exact s.q2_prime
  have hcopA : Nat.Coprime (diagonalA h s.m1 * r + 1) s.m1 := by
    rw [← hq₁, s.q1_prime.coprime_iff_not_dvd]
    exact s.q1_not_dvd_m1
  have hcopB : Nat.Coprime (diagonalB h s.m1 * r + 1) (s.m1 + h) := by
    rw [← hq₂, ← hm₂, s.q2_prime.coprime_iff_not_dvd]
    exact s.q2_not_dvd_m2
  have hphi : n.totient = diagonalGamma h s.m1 * r := by
    calc
      n.totient = (s.m1 * (diagonalA h s.m1 * r + 1)).totient :=
        congrArg Nat.totient hn
      _ = diagonalGamma h s.m1 * r :=
        diagonal_left_totient_eq_gamma_mul hprimeA hcopA
  refine ⟨r, s.sameSupportIndex_of_diagonal hdiag, hr, hn, hnshift,
    hprimeA, hprimeB, hcopA, hcopB, ?_⟩
  rw [← hphi]
  exact hcut

end RankAmplification
