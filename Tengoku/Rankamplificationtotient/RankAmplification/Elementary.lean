import Tengoku.Rankamplificationtotient.RankAmplification.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Elementary arithmetic lemmas This module contains the unconditional low-level facts used by the diagonal and provider arguments. -/

namespace RankAmplification

/-- The paper's convention for the largest prime factor at one.-/
@[simp]
theorem largestPrimeFactor_one : largestPrimeFactor 1 = 1 := by
  simp [largestPrimeFactor, primeSupport]

/-- The analogous harmless convention at zero.-/
@[simp]
theorem largestPrimeFactor_zero : largestPrimeFactor 0 = 1 := by
  simp [largestPrimeFactor, primeSupport]

/-- Equal prime support gives equal rational values of `φ(n) / n` for positive integers.-/
theorem totient_div_eq_of_primeSupport_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsupport : primeSupport a = primeSupport b) :
    (a.totient : ℚ) / a = (b.totient : ℚ) / b := by
  rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr ha),
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hb)]
  simpa [primeSupport] using congrArg
    (fun support : Finset ℕ ↦ ∏ p ∈ support, (1 - (p : ℚ)⁻¹)) hsupport

/-- The integral cross-multiplied form of `totient_div_eq_of_primeSupport_eq`.-/
theorem totient_mul_eq_of_primeSupport_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsupport : primeSupport a = primeSupport b) :
    a.totient * b = b.totient * a := by
  have hratio := totient_div_eq_of_primeSupport_eq ha hb hsupport
  have hcross : (a.totient : ℚ) * (b : ℚ) = (b.totient : ℚ) * (a : ℚ) :=
    (div_eq_div_iff (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)).mp hratio
  apply Nat.cast_injective (R := ℚ)
  simpa only [Nat.cast_mul] using hcross

/-- An odd shift cannot preserve prime support.-/
theorem not_isSameSupportIndex_of_odd {h j : ℕ} (hodd : Odd h) :
    ¬IsSameSupportIndex h j := by
  rintro ⟨hjpos, hsupport⟩
  have hjne : j ≠ 0 := Nat.ne_of_gt hjpos
  have hjhne : j + h ≠ 0 := by omega
  have htwo_dvd : 2 ∣ j ↔ 2 ∣ j + h := by
    constructor
    · intro hdvd
      have hmem : 2 ∈ primeSupport j :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd, hjne⟩
      rw [hsupport] at hmem
      exact Nat.dvd_of_mem_primeFactors hmem
    · intro hdvd
      have hmem : 2 ∈ primeSupport (j + h) :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd, hjhne⟩
      rw [← hsupport] at hmem
      exact Nat.dvd_of_mem_primeFactors hmem
  have heven : Even j ↔ Even (j + h) := by
    simpa only [even_iff_two_dvd] using htwo_dvd
  rcases Nat.even_or_odd j with hjeven | hjodd
  · have hjsum_even : Even (j + h) := heven.mp hjeven
    have hjodd' : Odd j := (Nat.even_add'.mp hjsum_even).mpr hodd
    exact (Nat.not_odd_iff_even.mpr hjeven) hjodd'
  · have hjsum_even : Even (j + h) :=
      Nat.even_add'.mpr ⟨fun _ ↦ hodd, fun _ ↦ hjodd⟩
    exact (Nat.not_even_iff_odd.mpr hjodd) (heven.mpr hjsum_even)

/-- For an odd shift, the same-support index set `J_h` is empty.-/
theorem sameSupportIndices_eq_empty_of_odd {h : ℕ} (hodd : Odd h) :
    sameSupportIndices h = ∅ := by
  ext j
  simp only [sameSupportIndices, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact not_isSameSupportIndex_of_odd hodd

/-- The two diagonal coefficients give the same cross-product.-/
theorem diagonal_mul_A_eq_mul_B (h j : ℕ) :
    j * diagonalA h j = (j + h) * diagonalB h j := by
  simp only [diagonalA, diagonalB, diagonalGCD]
  rw [← Nat.mul_div_assoc j (Nat.gcd_dvd_right j (j + h)),
    ← Nat.mul_div_assoc (j + h) (Nat.gcd_dvd_left j (j + h))]
  rw [Nat.mul_comm j (j + h)]

/-- The affine diagonal parametrization has shift exactly `h`.-/
theorem diagonal_affine_shift (h j r : ℕ) :
    j * (diagonalA h j * r + 1) + h =
      (j + h) * (diagonalB h j * r + 1) := by
  calc
    j * (diagonalA h j * r + 1) + h =
        (j * diagonalA h j) * r + (j + h) := by ring
    _ = ((j + h) * diagonalB h j) * r + (j + h) := by
      rw [diagonal_mul_A_eq_mul_B]
    _ = (j + h) * (diagonalB h j * r + 1) := by ring

/-- Equal support identifies the two common-totient coefficients in the diagonal.-/
theorem diagonalGamma_eq_totient_mul_B {h j : ℕ} (hsame : IsSameSupportIndex h j) :
    diagonalGamma h j = (j + h).totient * diagonalB h j := by
  obtain ⟨hjpos, hsupport⟩ := hsame
  have hjne : j ≠ 0 := Nat.ne_of_gt hjpos
  have hjhne : j + h ≠ 0 := by omega
  have hcross : j.totient * (j + h) = (j + h).totient * j :=
    totient_mul_eq_of_primeSupport_eq hjne hjhne hsupport
  have hdiv := congrArg (fun n : ℕ ↦ n / diagonalGCD h j) hcross
  simpa only [diagonalGamma, diagonalA, diagonalB, diagonalGCD,
    Nat.mul_div_assoc j.totient (Nat.gcd_dvd_right j (j + h)),
    Nat.mul_div_assoc (j + h).totient (Nat.gcd_dvd_left j (j + h))] using hdiv

/-- The first affine prime contributes exactly `Γ_j r` to the common totient.-/
theorem diagonal_left_totient_eq_gamma_mul {h j r : ℕ}
    (hprimeA : Nat.Prime (diagonalA h j * r + 1))
    (hcoprimeA : Nat.Coprime (diagonalA h j * r + 1) j) :
    (j * (diagonalA h j * r + 1)).totient = diagonalGamma h j * r := by
  rw [Nat.totient_mul hcoprimeA.symm, Nat.totient_prime hprimeA]
  simp only [Nat.add_sub_cancel, diagonalGamma]
  ring

/-- The prime-pair diagonal parametrization has equal totients.-/
theorem diagonal_parametrization_totient_eq {h j r : ℕ} (hsame : IsSameSupportIndex h j)
    (hprimeA : Nat.Prime (diagonalA h j * r + 1))
    (hprimeB : Nat.Prime (diagonalB h j * r + 1))
    (hcoprimeA : Nat.Coprime (diagonalA h j * r + 1) j)
    (hcoprimeB : Nat.Coprime (diagonalB h j * r + 1) (j + h)) :
    (j * (diagonalA h j * r + 1)).totient =
      ((j + h) * (diagonalB h j * r + 1)).totient := by
  rw [Nat.totient_mul hcoprimeA.symm, Nat.totient_mul hcoprimeB.symm,
    Nat.totient_prime hprimeA, Nat.totient_prime hprimeB]
  simp only [Nat.add_sub_cancel]
  calc
    j.totient * (diagonalA h j * r) =
        (j.totient * diagonalA h j) * r := by ring
    _ = ((j + h).totient * diagonalB h j) * r := by
      rw [← diagonalGamma_eq_totient_mul_B hsame]
      rfl
    _ = (j + h).totient * (diagonalB h j * r) := by ring

/-- Every diagonal representation is a genuine shifted equal-totient solution.-/
theorem IsDiagonalRepresentation.totient_eq {h Y n j r : ℕ}
    (hrep : IsDiagonalRepresentation h Y n j r) :
    n.totient = (n + h).totient := by
  rcases hrep with ⟨hsame, _, hn, hnh, hprimeA, hprimeB, hcoprimeA, hcoprimeB, _⟩
  calc
    n.totient = (j * (diagonalA h j * r + 1)).totient := congrArg Nat.totient hn
    _ = ((j + h) * (diagonalB h j * r + 1)).totient :=
      diagonal_parametrization_totient_eq hsame hprimeA hprimeB hcoprimeA hcoprimeB
    _ = (n + h).totient := (congrArg Nat.totient hnh).symm

/-- A diagonal representation identifies the common totient with `Γ_j r`.-/
theorem IsDiagonalRepresentation.totient_eq_gamma_mul {h Y n j r : ℕ}
    (hrep : IsDiagonalRepresentation h Y n j r) :
    n.totient = diagonalGamma h j * r := by
  rcases hrep with ⟨_, _, hn, _, hprimeA, _, hcoprimeA, _, _⟩
  calc
    n.totient = (j * (diagonalA h j * r + 1)).totient := congrArg Nat.totient hn
    _ = diagonalGamma h j * r :=
      diagonal_left_totient_eq_gamma_mul hprimeA hcoprimeA

/-- Every above-cutoff diagonal integer has equal shifted totients.-/
theorem IsAboveCutoffDiagonal.totient_eq {h Y n : ℕ}
    (hdiag : IsAboveCutoffDiagonal h Y n) :
    n.totient = (n + h).totient := by
  obtain ⟨_, _, hrep⟩ := hdiag
  exact hrep.totient_eq

/-- The cutoff in a diagonal representation is the cutoff of its actual common totient.-/
theorem IsAboveCutoffDiagonal.lt_largestPrimeFactor_totient {h Y n : ℕ}
    (hdiag : IsAboveCutoffDiagonal h Y n) :
    Y < largestPrimeFactor n.totient := by
  obtain ⟨j, r, hrep⟩ := hdiag
  rw [hrep.totient_eq_gamma_mul]
  exact hrep.2.2.2.2.2.2.2.2

/-- An odd shift has no above-cutoff diagonal representation.-/
theorem not_isAboveCutoffDiagonal_of_odd {h Y n : ℕ} (hodd : Odd h) :
    ¬IsAboveCutoffDiagonal h Y n := by
  rintro ⟨j, r, hrep⟩
  exact not_isSameSupportIndex_of_odd hodd hrep.1

/-- The finite above-cutoff diagonal set is empty for odd shifts.-/
theorem aboveCutoffDiagonalSet_eq_empty_of_odd {x h Y : ℕ} (hodd : Odd h) :
    aboveCutoffDiagonalSet x h Y = ∅ := by
  classical
  ext n
  simp [aboveCutoffDiagonalSet, not_isAboveCutoffDiagonal_of_odd hodd]

/-- The paper's diagonal counting function vanishes for odd shifts.-/
theorem aboveCutoffDiagonalCount_eq_zero_of_odd {x h Y : ℕ} (hodd : Odd h) :
    aboveCutoffDiagonalCount x h Y = 0 := by
  rw [aboveCutoffDiagonalCount, aboveCutoffDiagonalSet_eq_empty_of_odd hodd]
  rfl

/-- The above-cutoff diagonal is contained in the nonsmooth shifted-equality set.-/
theorem aboveCutoffDiagonalSet_subset_nonsmoothShiftedSet (x h Y : ℕ) :
    aboveCutoffDiagonalSet x h Y ⊆ nonsmoothShiftedSet x h Y := by
  classical
  intro n hn
  rw [aboveCutoffDiagonalSet, Finset.mem_filter] at hn
  rw [nonsmoothShiftedSet, Finset.mem_filter, shiftedEqualTotientSet, Finset.mem_filter]
  exact ⟨⟨hn.1, hn.2.totient_eq⟩, hn.2.lt_largestPrimeFactor_totient⟩

/-- Consequently, the diagonal count never exceeds the nonsmooth shifted count.-/
theorem aboveCutoffDiagonalCount_le_nonsmoothShiftedCount (x h Y : ℕ) :
    aboveCutoffDiagonalCount x h Y ≤ nonsmoothShiftedCount x h Y := by
  exact Finset.card_le_card (aboveCutoffDiagonalSet_subset_nonsmoothShiftedSet x h Y)

/-- Proposition 10.29: the classical `h = 2` family of equal totients.-/
theorem classical_h_two_family {t : ℕ} (hp : Nat.Prime (2 * t + 1))
    (hq : Nat.Prime (4 * t + 1)) :
    (2 * (4 * t + 1)).totient = (2 * (4 * t + 1) + 2).totient := by
  have hoddq : Odd (4 * t + 1) := ⟨2 * t, by omega⟩
  have hoddp : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hcoprimeTwoQ : Nat.Coprime 2 (4 * t + 1) := hoddq.coprime_two_left
  have hcoprimeFourP : Nat.Coprime 4 (2 * t + 1) := by
    rw [show 4 = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num)]
    exact hoddp.coprime_two_left
  have hshift : 2 * (4 * t + 1) + 2 = 4 * (2 * t + 1) := by omega
  have htotientFour : Nat.totient 4 = 2 := by decide
  rw [Nat.totient_mul hcoprimeTwoQ, hshift, Nat.totient_mul hcoprimeFourP,
    Nat.totient_two, htotientFour, Nat.totient_prime hq, Nat.totient_prime hp]
  omega

/-- The classical `h = 2` solution appears in the exact finite shifted-equality set.-/
theorem classical_h_two_family_mem_shiftedEqualTotientSet {t : ℕ}
    (hp : Nat.Prime (2 * t + 1)) (hq : Nat.Prime (4 * t + 1)) :
    2 * (4 * t + 1) ∈ shiftedEqualTotientSet (2 * (4 * t + 1)) 2 := by
  rw [shiftedEqualTotientSet, Finset.mem_filter]
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, classical_h_two_family hp hq⟩

/-- In particular, the exact `h = 2` counting function is positive at that solution.-/
theorem classical_h_two_family_count_pos {t : ℕ} (hp : Nat.Prime (2 * t + 1))
    (hq : Nat.Prime (4 * t + 1)) :
    0 < shiftedEqualTotientCount (2 * (4 * t + 1)) 2 := by
  rw [shiftedEqualTotientCount, Finset.card_pos]
  exact ⟨2 * (4 * t + 1), classical_h_two_family_mem_shiftedEqualTotientSet hp hq⟩

end RankAmplification
