/-
Exact signed incidence for the odd tails of two quartic rows.

`QuarticNormJaw` proves that the canonical odd tail at an inert prime
splits into two coprime jaws, one on the `p - 1` side and one on the
`p + 1` side.  It also proves that incident rows cannot share an odd
divisor across opposite sides.

This module closes the corresponding arithmetic interface: the complete
shared odd support is exactly the product of the two same-sign gcds.
Consequently that product, not merely an unspecified common tail, divides
the prime gap.

This is still a necessary condition.  It does not assert that either
same-sign gcd is nontrivial or large.
-/
import Tengoku.AgrawalR5.AgrawalCore.QuarticNormJaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- Each jaw is odd.-/
theorem quarticMinusJaw_coprime_two
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    Nat.Coprime (quarticMinusJaw p hp5) 2 := by
  have htail :
      Nat.Coprime (quarticOddTail p hp5) 2 :=
    Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 10)
      (quarticOddTail_coprime_ten hp hp5)
  exact Nat.Coprime.of_dvd_left
    (quarticMinusJaw_dvd_oddTail hp hp5) htail

theorem quarticPlusShadow_coprime_two
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    Nat.Coprime (quarticPlusShadow p hp5) 2 := by
  have htail :
      Nat.Coprime (quarticOddTail p hp5) 2 :=
    Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 10)
      (quarticOddTail_coprime_ten hp hp5)
  exact Nat.Coprime.of_dvd_left
    (quarticPlusShadow_dvd_oddTail hp5) htail

/-- Opposite jaws of two incident rows are genuinely coprime, rather than
merely having every common divisor divide `2`.-/
theorem quarticCrossJaws_coprime_of_incidence
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hpr : p ≤ r)
    (hgap :
      Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ∣ r - p) :
    Nat.Coprime (quarticMinusJaw p hp5) (quarticPlusShadow r hr5)
      ∧
    Nat.Coprime (quarticPlusShadow p hp5) (quarticMinusJaw r hr5) := by
  obtain ⟨hforward, hreverse⟩ :=
    quarticCrossJaws_partition_of_incidence
      hp hr hp5 hr5 hpr hgap
  constructor
  · rw [Nat.coprime_iff_gcd_eq_one]
    let g :=
      Nat.gcd (quarticMinusJaw p hp5) (quarticPlusShadow r hr5)
    have hg2 : g ∣ 2 :=
      hforward g (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    exact Nat.eq_one_of_dvd_coprimes
      (quarticMinusJaw_coprime_two hp hp5)
      (Nat.gcd_dvd_left _ _) hg2
  · rw [Nat.coprime_iff_gcd_eq_one]
    let g :=
      Nat.gcd (quarticPlusShadow p hp5) (quarticMinusJaw r hr5)
    have hg2 : g ∣ 2 :=
      hreverse g (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    exact Nat.eq_one_of_dvd_coprimes
      (quarticPlusShadow_coprime_two hp hp5)
      (Nat.gcd_dvd_left _ _) hg2

/-- **Exact signed factorization of shared odd support.**

For incident inert rows, the gcd of the two complete odd tails is exactly
the product of the two same-sign gcds.  Cross terms disappear because they
are coprime, and the two jaws at either endpoint are already coprime.-/
theorem quarticSharedTail_gcd_eq_sameSignProduct_of_incidence
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hpr : p ≤ r)
    (hgap :
      Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ∣ r - p) :
    Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) =
      Nat.gcd (quarticMinusJaw p hp5) (quarticMinusJaw r hr5) *
      Nat.gcd (quarticPlusShadow p hp5) (quarticPlusShadow r hr5) := by
  obtain ⟨hminusPlus, hplusMinus⟩ :=
    quarticCrossJaws_coprime_of_incidence
      hp hr hp5 hr5 hpr hgap
  rw [quarticOddTail_eq_mul_jaws hp hp5,
    quarticOddTail_eq_mul_jaws hr hr5]
  rw [Nat.Coprime.gcd_mul
    (quarticMinusJaw p hp5 * quarticPlusShadow p hp5)
    (quarticJaws_coprime hr hr5)]
  have hleft :
      Nat.gcd
          (quarticMinusJaw p hp5 * quarticPlusShadow p hp5)
          (quarticMinusJaw r hr5) =
        Nat.gcd (quarticMinusJaw p hp5) (quarticMinusJaw r hr5) := by
    rw [mul_comm]
    exact hplusMinus.gcd_mul_left_cancel _
  have hright :
      Nat.gcd
          (quarticMinusJaw p hp5 * quarticPlusShadow p hp5)
          (quarticPlusShadow r hr5) =
        Nat.gcd (quarticPlusShadow p hp5) (quarticPlusShadow r hr5) := by
    exact hminusPlus.gcd_mul_left_cancel _
  rw [hleft, hright]

/-- The product of the two same-sign overlaps divides the prime gap.-/
theorem quarticSameSignIncidenceProduct_dvd_gap
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hpr : p ≤ r)
    (hgap :
      Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ∣ r - p) :
    Nat.gcd (quarticMinusJaw p hp5) (quarticMinusJaw r hr5) *
        Nat.gcd (quarticPlusShadow p hp5) (quarticPlusShadow r hr5)
      ∣ r - p := by
  rw [← quarticSharedTail_gcd_eq_sameSignProduct_of_incidence
    hp hr hp5 hr5 hpr hgap]
  exact hgap

/-- Literal two-row form of the signed incidence law.-/
theorem quarticRows_sameSignIncidenceProduct_dvd_gap
    {p r q : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hpr : p ≤ r) (hq0 : 0 < q)
    (hrowp : r * q ≡ 1 [MOD quarticOrderModulus p hp5]
      ∨ r * q ≡ p ^ 2 [MOD quarticOrderModulus p hp5])
    (hrowr : p * q ≡ 1 [MOD quarticOrderModulus r hr5]
      ∨ p * q ≡ r ^ 2 [MOD quarticOrderModulus r hr5]) :
    Nat.gcd (quarticMinusJaw p hp5) (quarticMinusJaw r hr5) *
        Nat.gcd (quarticPlusShadow p hp5) (quarticPlusShadow r hr5)
      ∣ r - p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hr0 : 0 < r := (Fact.out : r.Prime).pos
  have hdP : quarticOddTail p hp5 ∣ r * q - 1 :=
    quarticRow_oddTail_dvd_sub_one hp hp5
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hr0) (Nat.ne_of_gt hq0))) hrowp
  have hdR : quarticOddTail r hr5 ∣ p * q - 1 :=
    quarticRow_oddTail_dvd_sub_one hr hr5
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hp0) (Nat.ne_of_gt hq0))) hrowr
  have hgap :
      Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ∣ r - p :=
    sharedOddSupport_dvd_gap hpr
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hr0) (Nat.ne_of_gt hq0)))
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hp0) (Nat.ne_of_gt hq0)))
      hdP hdR
  exact quarticSameSignIncidenceProduct_dvd_gap
    hp hr hp5 hr5 hpr hgap

/-- **Signed incidence triangle.**

For three ordered inert factors carrying all three literal rows, each
prime gap is divisible by the product of its minus-minus overlap and its
plus-plus overlap.  Thus the unsigned triangle of `OddTailTriangle`
decomposes canonically into two disjoint signed triangles.-/
theorem quarticSignedIncidenceTriangle
    {p r q : ℕ} [Fact p.Prime] [Fact r.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hq5 : q ≠ 5)
    (hpr : p ≤ r) (hrq : r ≤ q)
    (hrowp : r * q ≡ 1 [MOD quarticOrderModulus p hp5]
      ∨ r * q ≡ p ^ 2 [MOD quarticOrderModulus p hp5])
    (hrowr : p * q ≡ 1 [MOD quarticOrderModulus r hr5]
      ∨ p * q ≡ r ^ 2 [MOD quarticOrderModulus r hr5])
    (hrowq : p * r ≡ 1 [MOD quarticOrderModulus q hq5]
      ∨ p * r ≡ q ^ 2 [MOD quarticOrderModulus q hq5]) :
    Nat.gcd (quarticMinusJaw p hp5) (quarticMinusJaw r hr5) *
          Nat.gcd (quarticPlusShadow p hp5) (quarticPlusShadow r hr5)
        ∣ r - p
      ∧
    Nat.gcd (quarticMinusJaw p hp5) (quarticMinusJaw q hq5) *
          Nat.gcd (quarticPlusShadow p hp5) (quarticPlusShadow q hq5)
        ∣ q - p
      ∧
    Nat.gcd (quarticMinusJaw r hr5) (quarticMinusJaw q hq5) *
          Nat.gcd (quarticPlusShadow r hr5) (quarticPlusShadow q hq5)
        ∣ q - r := by
  rcases quarticOddTail_incidenceTriangle
      hp hr hq hp5 hr5 hq5 hpr hrq hrowp hrowr hrowq with
    ⟨hgapPR, hgapPQ, hgapRQ⟩
  have hpq : p ≤ q := hpr.trans hrq
  exact ⟨
    quarticSameSignIncidenceProduct_dvd_gap
      hp hr hp5 hr5 hpr hgapPR,
    quarticSameSignIncidenceProduct_dvd_gap
      hp hq hp5 hq5 hpq hgapPQ,
    quarticSameSignIncidenceProduct_dvd_gap
      hr hq hr5 hq5 hrq hgapRQ⟩

end AgrawalCore
