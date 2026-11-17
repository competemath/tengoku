/-
Exact transport between the final local row and one earlier row.

This module isolates two logically different statements:

* a genuine compatibility obstruction modulo `gcd Tₚ T_q`, independent of
  the final-row multiplier;
* exact linear normal forms for the remaining multiplier-dependent lift.

No finite census or asymptotic assertion is formalized here.
-/
import Tengoku.Seed.Data.Nat.ModEq
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- **Two-row transport.**

If the final row gives `P ≡ c (mod Tq)` and an earlier row, after
multiplication by its prime, gives `Pq ≡ a (mod Tp)`, then their common
reduction forces

`cq ≡ a (mod gcd Tp Tq)`.

Unlike either input row alone, this necessary condition couples the two order
moduli and no longer contains the final-row multiplier.
@isnad1 id=modeq.2h6v.s5.320a6857ce91 from=translated src=- shape=75e0723d vocab=6a148691
-/
theorem finalSmallRow_transport {P c q a Tp Tq : ℕ}
    (hfinal : P ≡ c [MOD Tq]) (hsmall : P * q ≡ a [MOD Tp]) :
    c * q ≡ a [MOD Nat.gcd Tp Tq] := by
  have hqfinal : P * q ≡ c * q [MOD Nat.gcd Tp Tq] :=
    (hfinal.of_dvd (Nat.gcd_dvd_right Tp Tq)).mul_right q
  have hqsmall : P * q ≡ a [MOD Nat.gcd Tp Tq] :=
    hsmall.of_dvd (Nat.gcd_dvd_left Tp Tq)
  exact hqfinal.symm.trans hqsmall

/-- Pure-branch transport: `P ≡ 1 (mod Tq)` forces
`q ≡ a (mod gcd Tp Tq)`.
@isnad1 id=modeq.2h5v.s5.45a538476c7a from=translated src=- shape=08459867 vocab=6a148691
-/
theorem pureSmallRow_transport {P q a Tp Tq : ℕ}
    (hfinal : P ≡ 1 [MOD Tq]) (hsmall : P * q ≡ a [MOD Tp]) :
    q ≡ a [MOD Nat.gcd Tp Tq] := by
  simpa using finalSmallRow_transport hfinal hsmall

/-- Twisted-branch transport: `P ≡ q² (mod Tq)` forces
`q³ ≡ a (mod gcd Tp Tq)`.
@isnad1 id=modeq.2h5v.s6.825a861d6c39 from=translated src=- shape=df218589 vocab=ca8eebdf
-/
theorem twistedSmallRow_transport {P q a Tp Tq : ℕ}
    (hfinal : P ≡ q ^ 2 [MOD Tq]) (hsmall : P * q ≡ a [MOD Tp]) :
    q ^ 3 ≡ a [MOD Nat.gcd Tp Tq] := by
  have h := finalSmallRow_transport hfinal hsmall
  convert h using 1
  ring

/-- **The third side of the CRT triangle.**

Two earlier rows involving the same product `P * q` must agree after
reduction to the common divisor of their order moduli:

`a ≡ b (mod gcd Tp Tr)`.

Together with the two transports from the final row, this is the complete
pairwise compatibility condition for the three residue classes.
@isnad1 id=modeq.2h6v.s5.f262f128fb31 from=translated src=- shape=02ab665c vocab=6a148691
-/
theorem smallRows_triangle {P q a b Tp Tr : ℕ}
    (hp : P * q ≡ a [MOD Tp]) (hr : P * q ≡ b [MOD Tr]) :
    a ≡ b [MOD Nat.gcd Tp Tr] := by
  have hp' : P * q ≡ a [MOD Nat.gcd Tp Tr] :=
    hp.of_dvd (Nat.gcd_dvd_left Tp Tr)
  have hr' : P * q ≡ b [MOD Nat.gcd Tp Tr] :=
    hr.of_dvd (Nat.gcd_dvd_right Tp Tr)
  exact hp'.symm.trans hr'

/-- **Branch-independent odd shadow of a local row.**

Let `D` be a divisor of the local order on which `p² ≡ 1`.  Then both
possible local residues, `1` and `p²`, collapse to the single Korselt-type
condition `P ≡ 1 (mod D)`.

In the inert Agrawal branch, `D` is the odd part of the order away from `5`;
the structural bound `D ∣ p² - 1` supplies `hp`.  The theorem deliberately
keeps that field-theoretic input separate from its arithmetic kernel.
@isnad1 id=modeq.3h4v.s6.715ed08693f8 from=translated src=- shape=9e6b1aa4 vocab=a3f3ab3b
-/
theorem localRow_oddShadow {P p T D : ℕ}
    (hDT : D ∣ T) (hp : p ^ 2 ≡ 1 [MOD D])
    (hrow : P ≡ 1 [MOD T] ∨ P ≡ p ^ 2 [MOD T]) :
    P ≡ 1 [MOD D] := by
  rcases hrow with hrow | hrow
  · exact hrow.of_dvd hDT
  · exact (hrow.of_dvd hDT).trans hp

/-- A unit congruence `a*b ≡ 1 (mod D)`, written as a divisibility in
natural numbers, forces `b` to be coprime to `D`.
@isnad1 id=coprime.2h3v.s5.9b24b9865449 from=translated src=- shape=9050d561 vocab=60875059
-/
theorem coprime_right_of_dvd_mul_sub_one {a b D : ℕ}
    (hab : 1 ≤ a * b) (h : D ∣ a * b - 1) :
    Nat.Coprime b D := by
  let g := Nat.gcd b D
  have hgb : g ∣ b := Nat.gcd_dvd_left b D
  have hgD : g ∣ D := Nat.gcd_dvd_right b D
  have hgprod : g ∣ a * b := dvd_mul_of_dvd_right hgb a
  have hgsub : g ∣ a * b - 1 := hgD.trans h
  have hg1 : g ∣ 1 := by
    have hd := Nat.dvd_sub hgprod hgsub
    simpa only [Nat.sub_sub_self hab] using hd
  exact Nat.dvd_one.mp hg1

/-- **Shared odd support divides the prime gap.**

If the odd shadows attached to `p` and `r` both divide their complementary
products, then their common part divides `r-p`.  Thus a prime-power component
shared by two local order moduli must also occur in the corresponding gap
between the two prime factors.

This is the incidence form of the third CRT side after the exponents have
collapsed on the odd order support.
@isnad1 id=dvd.5h5v.s6.92cffc7430da from=translated src=- shape=d53b8d3e vocab=2b3e5264
-/
theorem sharedOddSupport_dvd_gap {p r q Dp Dr : ℕ}
    (hpr : p ≤ r) (hpos : 1 ≤ r * q) (hpqpos : 1 ≤ p * q)
    (hp : Dp ∣ r * q - 1) (hr : Dr ∣ p * q - 1) :
    Nat.gcd Dp Dr ∣ r - p := by
  let d := Nat.gcd Dp Dr
  have hdp : d ∣ r * q - 1 := (Nat.gcd_dvd_left Dp Dr).trans hp
  have hdr : d ∣ p * q - 1 := (Nat.gcd_dvd_right Dp Dr).trans hr
  have hpq_le : p * q - 1 ≤ r * q - 1 := by
    have hpq : p * q ≤ r * q := Nat.mul_le_mul_right q hpr
    omega
  have hdiff : d ∣ (r - p) * q := by
    have hd := Nat.dvd_sub hdp hdr
    have hsub :
        (r * q - 1) - (p * q - 1) = r * q - p * q := by
      omega
    rw [hsub, ← Nat.sub_mul] at hd
    exact hd
  have hcop : Nat.Coprime q d :=
    coprime_right_of_dvd_mul_sub_one hpos hdp
  exact hcop.symm.dvd_of_dvd_mul_right hdiff

/-- Exact multiplier normal form in the pure branch `P = 1 + hTq`.
@isnad1 id=iff.0h5v.s6.7808fddacb86 from=translated src=- shape=8cfe58fc vocab=5c8a169d
-/
theorem pureSmallRow_lift_iff {h q Tq a Tp : ℕ} :
    (1 + h * Tq) * q ≡ a [MOD Tp] ↔
      q + (q * Tq) * h ≡ a [MOD Tp] := by
  have heq : (1 + h * Tq) * q = q + (q * Tq) * h := by ring
  rw [heq]

/-- Exact multiplier normal form in the twisted branch
`P + hTq = q²`.  It uses addition only, so no truncated natural-number
subtraction enters the certified statement.
@isnad1 id=iff.1h6v.s6.2058675fdfe3 from=translated src=- shape=6994b957 vocab=91cc838f
-/
theorem twistedSmallRow_lift_iff {P h q Tq a Tp : ℕ}
    (hP : P + h * Tq = q ^ 2) :
    P * q ≡ a [MOD Tp] ↔
      a + (q * Tq) * h ≡ q ^ 3 [MOD Tp] := by
  have heq : P * q + (q * Tq) * h = q ^ 3 := by
    calc
      P * q + (q * Tq) * h = (P + h * Tq) * q := by ring
      _ = q ^ 2 * q := by rw [hP]
      _ = q ^ 3 := by ring
  constructor
  · intro hr
    have hadd := hr.add (Nat.ModEq.refl ((q * Tq) * h))
    rw [heq] at hadd
    exact hadd.symm
  · intro hr
    rw [← heq] at hr
    have hcancel := Nat.ModEq.add_right_cancel
      (Nat.ModEq.refl ((q * Tq) * h)) hr
    exact hcancel.symm

/-- **Bounded-lift exclusion.**

Two distinct representatives below the modulus cannot be congruent.  In the
fibre audit, `h ≤ H < M` is the exact multiplier interval, while `h₀` is the
canonical solution of the reduced linear congruence.  Thus `H < h₀ < M`
certifies that the row has no admissible lift.
@isnad1 id=not.4h4v.s5.d4e5dc04b5e4 from=translated src=- shape=f015624f vocab=b6e0e5a7
-/
theorem boundedLift_exclusion {h H h₀ M : ℕ}
    (hh : h ≤ H) (hH₀ : H < h₀) (h₀M : h₀ < M) (hHM : H < M) :
    ¬ h ≡ h₀ [MOD M] := by
  intro hmod
  have hhM : h < M := lt_of_le_of_lt hh hHM
  have heq : h = h₀ := hmod.eq_of_lt_of_lt hhM h₀M
  omega

end AgrawalCore
