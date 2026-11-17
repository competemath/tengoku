/-
The canonical odd tail of the quartic order rows.

For a good inert prime `p`, the concrete quartic modulus divides
`10 * (p^2 - 1)`.  Removing its complete `2`- and `5`-primary parts
therefore leaves a canonical divisor of `p^2 - 1`.  Both branches of the
quartic row collapse modulo this tail.

The final theorem records the resulting incidence matrix for three rows:
the common odd support attached to any two factors divides their prime gap.
-/
import Tengoku.AgrawalR5.AgrawalCore.CyclotomicDyadic
import Tengoku.AgrawalR5.AgrawalCore.TwoRowTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- Remove the complete `2`- and `5`-primary parts from the concrete
quartic order modulus.-/
noncomputable def quarticOddTail (p : ℕ) [Fact p.Prime]
    (hp5 : p ≠ 5) : ℕ :=
  ordCompl[5] (ordCompl[2] (quarticOrderModulus p hp5))

/-- The concrete quartic modulus is bounded arithmetically:
`T_p ∣ 10 * (p² - 1)`.
@isnad1 id=dvd.2h1v.s6.127c5bb37b57 from=translated src=- shape=554e86b5 vocab=ab9f74be
-/
theorem quarticOrderModulus_dvd_ten_mul_sq_sub_one
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    quarticOrderModulus p hp5 ∣ 10 * (p * p - 1) := by
  let u := localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hu : u ^ (10 * (p * p - 1)) = 1 := by
    rw [mul_comm, pow_mul]
    rw [localCyclotomicUnit_pow_sq_sub_one hp hp5 (by omega)]
    exact inertTwistUnit_pow_ten
  have hord : orderOf u ∣ 10 * (p * p - 1) :=
    orderOf_dvd_of_pow_eq_one hu
  unfold quarticOrderModulus
  apply Nat.lcm_dvd hord
  exact dvd_mul_of_dvd_left (by norm_num : 5 ∣ 10) _

/-- The canonical odd tail divides the full quartic modulus.
@isnad1 id=dvd.1h1v.s4.877b7ba3517d from=translated src=- shape=c2faa8c9 vocab=ec010e9f
-/
theorem quarticOddTail_dvd_modulus (hp5 : p ≠ 5) :
    quarticOddTail p hp5 ∣ quarticOrderModulus p hp5 := by
  exact (Nat.ordCompl_dvd _ 5).trans (Nat.ordCompl_dvd _ 2)

/-- The canonical odd tail is prime to `10`.
@isnad1 id=coprime.2h1v.s6.d08ae5ce0e8e from=translated src=- shape=2bc8419c vocab=66597802
-/
theorem quarticOddTail_coprime_ten
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    Nat.Coprime (quarticOddTail p hp5) 10 := by
  have hT0 : quarticOrderModulus p hp5 ≠ 0 := by
    intro hzero
    have hdvd :=
      quarticOrderModulus_dvd_ten_mul_sq_sub_one hp hp5
    rw [hzero] at hdvd
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hpp : 4 ≤ p * p := Nat.mul_le_mul hpge hpge
    have hpos : 10 * (p * p - 1) ≠ 0 := by omega
    exact hpos (Nat.eq_zero_of_zero_dvd hdvd)
  have h2tail0 : ordCompl[2] (quarticOrderModulus p hp5) ≠ 0 := by
    intro hzero
    have hsplit :=
      Nat.ordProj_mul_ordCompl_eq_self (quarticOrderModulus p hp5) 2
    rw [hzero, mul_zero] at hsplit
    exact hT0 hsplit.symm
  have htwo :
      Nat.Coprime (quarticOddTail p hp5) 2 := by
    apply Nat.Coprime.of_dvd_left (Nat.ordCompl_dvd _ 5)
    exact (Nat.coprime_ordCompl Nat.prime_two hT0).symm
  have hfive :
      Nat.Coprime (quarticOddTail p hp5) 5 :=
    (Nat.coprime_ordCompl (by norm_num : Nat.Prime 5) h2tail0).symm
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    Nat.coprime_mul_iff_right]
  exact ⟨htwo, hfive⟩

/-- **Odd-tail field bound.**

Every prime-power component of the quartic modulus away from `2` and `5`
already occurs in `p² - 1`.
@isnad1 id=dvd.2h1v.s6.36038f02d305 from=translated src=- shape=9aaf742b vocab=19509c42
-/
theorem quarticOddTail_dvd_sq_sub_one
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    quarticOddTail p hp5 ∣ p * p - 1 := by
  have hten :
      quarticOddTail p hp5 ∣ 10 * (p * p - 1) :=
    (quarticOddTail_dvd_modulus hp5).trans
      (quarticOrderModulus_dvd_ten_mul_sq_sub_one hp hp5)
  exact (quarticOddTail_coprime_ten hp hp5).dvd_mul_left.mp hten

/-- Both quartic branches collapse to `1` modulo the canonical odd tail.
@isnad1 id=modeq.3h2v.s6.450995291c1c from=translated src=- shape=63c1b231 vocab=02206ab6
-/
theorem quarticRow_oddTailShadow {P : ℕ}
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5)
    (hrow : P ≡ 1 [MOD quarticOrderModulus p hp5]
      ∨ P ≡ p ^ 2 [MOD quarticOrderModulus p hp5]) :
    P ≡ 1 [MOD quarticOddTail p hp5] := by
  have hpSq : p ^ 2 ≡ 1 [MOD quarticOddTail p hp5] := by
    have hd := quarticOddTail_dvd_sq_sub_one hp hp5
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hpp : 4 ≤ p * p := Nat.mul_le_mul hpge hpge
    exact ((Nat.modEq_iff_dvd' (by simpa [pow_two] using
      (show 1 ≤ p * p by omega))).mpr
      (by simpa [pow_two] using hd)).symm
  exact localRow_oddShadow (quarticOddTail_dvd_modulus hp5) hpSq hrow

/-- Divisibility form of the odd shadow.
@isnad1 id=dvd.4h2v.s6.94dbdac84686 from=translated src=- shape=4b514a03 vocab=ad3f53a9
-/
theorem quarticRow_oddTail_dvd_sub_one {P : ℕ}
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5)
    (hP : 1 ≤ P)
    (hrow : P ≡ 1 [MOD quarticOrderModulus p hp5]
      ∨ P ≡ p ^ 2 [MOD quarticOrderModulus p hp5]) :
    quarticOddTail p hp5 ∣ P - 1 := by
  exact (Nat.modEq_iff_dvd' hP).mp
    (quarticRow_oddTailShadow hp hp5 hrow).symm

/-- **Canonical odd-support incidence triangle.**

For three ordered good inert primes, assume their three literal quartic
rows.  The common canonical odd tail attached to any pair divides the gap
between those two primes:

`gcd(D_p,D_r) ∣ r-p`, `gcd(D_p,D_q) ∣ q-p`, and
`gcd(D_r,D_q) ∣ q-r`.

This is the full three-row specialization of `sharedOddSupport_dvd_gap`.
It is a necessary condition only; it does not assert that the three gcds
are large.
@isnad1 id=and.11h3v.s8.99a46b8b2614 from=translated src=- shape=877fca56 vocab=c28f622a
-/
theorem quarticOddTail_incidenceTriangle
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
    Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ∣ r - p
      ∧ Nat.gcd (quarticOddTail p hp5) (quarticOddTail q hq5) ∣ q - p
      ∧ Nat.gcd (quarticOddTail r hr5) (quarticOddTail q hq5) ∣ q - r := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hr0 : 0 < r := (Fact.out : r.Prime).pos
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hdP : quarticOddTail p hp5 ∣ r * q - 1 :=
    quarticRow_oddTail_dvd_sub_one hp hp5
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hr0) (Nat.ne_of_gt hq0))) hrowp
  have hdR : quarticOddTail r hr5 ∣ p * q - 1 :=
    quarticRow_oddTail_dvd_sub_one hr hr5
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hp0) (Nat.ne_of_gt hq0))) hrowr
  have hdQ : quarticOddTail q hq5 ∣ p * r - 1 :=
    quarticRow_oddTail_dvd_sub_one hq hq5
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hp0) (Nat.ne_of_gt hr0))) hrowq
  have hpq : p ≤ q := hpr.trans hrq
  refine ⟨sharedOddSupport_dvd_gap hpr
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hr0) (Nat.ne_of_gt hq0)))
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hp0) (Nat.ne_of_gt hq0)))
      hdP hdR, ?_, ?_⟩
  · apply sharedOddSupport_dvd_gap (p := p) (r := q) (q := r) hpq
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hq0) (Nat.ne_of_gt hr0)))
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hp0) (Nat.ne_of_gt hr0)))
    · simpa [Nat.mul_comm] using hdP
    · exact hdQ
  · apply sharedOddSupport_dvd_gap (p := r) (r := q) (q := p) hrq
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hq0) (Nat.ne_of_gt hp0)))
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.ne_of_gt hr0) (Nat.ne_of_gt hp0)))
    · simpa [Nat.mul_comm] using hdR
    · simpa [Nat.mul_comm] using hdQ

/-- Strictly ordered factors turn the three incidence divisibilities into
three sharp upper bounds for the shared odd supports.  Consequently, any
one reversed strict inequality is an exact certificate that the three
quartic rows cannot coexist.
@isnad1 id=and.11h3v.s8.2641b3b42ea6 from=translated src=- shape=877fca56 vocab=b0d1aba7
-/
theorem quarticOddTail_incidenceBounds
    {p r q : ℕ} [Fact p.Prime] [Fact r.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hq5 : q ≠ 5)
    (hpr : p < r) (hrq : r < q)
    (hrowp : r * q ≡ 1 [MOD quarticOrderModulus p hp5]
      ∨ r * q ≡ p ^ 2 [MOD quarticOrderModulus p hp5])
    (hrowr : p * q ≡ 1 [MOD quarticOrderModulus r hr5]
      ∨ p * q ≡ r ^ 2 [MOD quarticOrderModulus r hr5])
    (hrowq : p * r ≡ 1 [MOD quarticOrderModulus q hq5]
      ∨ p * r ≡ q ^ 2 [MOD quarticOrderModulus q hq5]) :
    Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ≤ r - p
      ∧ Nat.gcd (quarticOddTail p hp5) (quarticOddTail q hq5) ≤ q - p
      ∧ Nat.gcd (quarticOddTail r hr5) (quarticOddTail q hq5) ≤ q - r := by
  rcases quarticOddTail_incidenceTriangle hp hr hq hp5 hr5 hq5
      hpr.le hrq.le hrowp hrowr hrowq with ⟨hPR, hPQ, hRQ⟩
  exact ⟨Nat.le_of_dvd (by omega) hPR,
    Nat.le_of_dvd (by omega) hPQ,
    Nat.le_of_dvd (by omega) hRQ⟩

/-- A single oversized shared odd support excludes a complete row
triangle.  This is the directly executable form of the odd-tail sieve.
@isnad1 id=false.12h3v.s8.ea3c5da8c541 from=translated src=- shape=385e0e2b vocab=052a952e
-/
theorem quarticOddTail_oversize_exclusion
    {p r q : ℕ} [Fact p.Prime] [Fact r.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hq5 : q ≠ 5)
    (hpr : p < r) (hrq : r < q)
    (hrowp : r * q ≡ 1 [MOD quarticOrderModulus p hp5]
      ∨ r * q ≡ p ^ 2 [MOD quarticOrderModulus p hp5])
    (hrowr : p * q ≡ 1 [MOD quarticOrderModulus r hr5]
      ∨ p * q ≡ r ^ 2 [MOD quarticOrderModulus r hr5])
    (hrowq : p * r ≡ 1 [MOD quarticOrderModulus q hq5]
      ∨ p * r ≡ q ^ 2 [MOD quarticOrderModulus q hq5])
    (hlarge :
      r - p < Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5)
      ∨ q - p < Nat.gcd (quarticOddTail p hp5) (quarticOddTail q hq5)
      ∨ q - r < Nat.gcd (quarticOddTail r hr5) (quarticOddTail q hq5)) :
    False := by
  rcases quarticOddTail_incidenceBounds hp hr hq hp5 hr5 hq5
      hpr hrq hrowp hrowr hrowq with ⟨hPR, hPQ, hRQ⟩
  rcases hlarge with hlarge | hlarge | hlarge <;> omega

end AgrawalCore
