/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The definition of `f` follows the Apache-2.0-licensed Formal Conjectures
statement of Erdős problem 700 (Copyright 2026 The Formal Conjectures Authors):
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/700.lean
The proofs below are independent; that statement file is not imported.
-/
import Tengoku.Jsp000570Lean.Erdos700.Lucas
import Tengoku.Seed.Data.Nat.Prime.Basic
import Tengoku.Seed.Data.Nat.GCD.Basic
import Tengoku.Seed.Order.Lattice.Nat
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Tauto

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From six pair exclusions to the exact minimum

This file proves the final arithmetic reduction for four ordered primes.
The digit restrictions are not hypotheses here: the input
is simply that no two prime divisors are simultaneously absent from a binomial.
-/

namespace Erdos700

/-- The function in Erdős problem 700. For an empty index range, `sInf` is zero.-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

/-- At least three of the four displayed integers divide `m`.-/
def ThreeOfFour (p q r s m : ℕ) : Prop :=
  (p ∣ m ∧ q ∣ m ∧ r ∣ m) ∨
  (p ∣ m ∧ q ∣ m ∧ s ∣ m) ∨
  (p ∣ m ∧ r ∣ m ∧ s ∣ m) ∨
  (q ∣ m ∧ r ∣ m ∧ s ∣ m)

/-- The six pairwise exclusions established by the digit arguments.-/
def NoTwoMissing (p q r s m : ℕ) : Prop :=
  ¬ (¬ p ∣ m ∧ ¬ q ∣ m) ∧
  ¬ (¬ p ∣ m ∧ ¬ r ∣ m) ∧
  ¬ (¬ p ∣ m ∧ ¬ s ∣ m) ∧
  ¬ (¬ q ∣ m ∧ ¬ r ∣ m) ∧
  ¬ (¬ q ∣ m ∧ ¬ s ∣ m) ∧
  ¬ (¬ r ∣ m ∧ ¬ s ∣ m)

theorem threeOfFour_of_noTwoMissing (p q r s m : ℕ)
    (h : NoTwoMissing p q r s m) : ThreeOfFour p q r s m := by
  unfold NoTwoMissing at h
  unfold ThreeOfFour
  tauto

/-- Pairwise distinct primes dividing an integer have their product dividing it.-/
theorem three_primes_mul_dvd (p q r m : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpm : p ∣ m) (hqm : q ∣ m) (hrm : r ∣ m) : p * q * r ∣ m := by
  have cpq : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have cpr : p.Coprime r := (Nat.coprime_primes hp hr).mpr hpr
  have cqr : q.Coprime r := (Nat.coprime_primes hq hr).mpr hqr
  exact (cpr.mul_left cqr).mul_dvd_of_dvd_of_dvd
    (cpq.mul_dvd_of_dvd_of_dvd hpm hqm) hrm

/-- A prime dividing the row divides its binomial at any other prime index.-/
theorem dvd_choose_other_prime (p s n : ℕ) (hp : p.Prime) (hs : s.Prime)
    (hpn : p ∣ n) (hne : p ≠ s) : p ∣ n.choose s := by
  by_contra h
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hs).mp
    (dvd_of_not_dvd_choose p n s hp hpn h))

/-- The smallest possible product of three of four ordered prime divisors
is a lower bound for the gcd whenever at least three are present.-/
theorem gcd_four_primes_ge_of_threeOfFour (p q r s m : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (h : ThreeOfFour p q r s m) :
    p * q * r ≤ Nat.gcd (p * q * r * s) m := by
  have hpr : p < r := lt_trans hpq hqr
  have hps : p < s := lt_trans hpr hrs
  have hqs : q < s := lt_trans hqr hrs
  have hgpos : 0 < Nat.gcd (p * q * r * s) m :=
    Nat.gcd_pos_of_pos_left m (mul_pos (mul_pos (mul_pos hp.pos hq.pos) hr.pos) hs.pos)
  rcases h with h | h | h | h
  · have hmul := three_primes_mul_dvd p q r m hp hq hr
      (ne_of_lt hpq) (ne_of_lt hpr) (ne_of_lt hqr) h.1 h.2.1 h.2.2
    exact Nat.le_of_dvd hgpos (Nat.dvd_gcd ⟨s, rfl⟩ hmul)
  · have hmul := three_primes_mul_dvd p q s m hp hq hs
      (ne_of_lt hpq) (ne_of_lt hps) (ne_of_lt hqs) h.1 h.2.1 h.2.2
    have hd : p * q * s ∣ Nat.gcd (p * q * r * s) m :=
      Nat.dvd_gcd ⟨r, by ring⟩ hmul
    exact (Nat.mul_le_mul_left (p * q) hrs.le).trans (Nat.le_of_dvd hgpos hd)
  · have hmul := three_primes_mul_dvd p r s m hp hr hs
      (ne_of_lt hpr) (ne_of_lt hps) (ne_of_lt hrs) h.1 h.2.1 h.2.2
    have hd : p * r * s ∣ Nat.gcd (p * q * r * s) m :=
      Nat.dvd_gcd ⟨q, by ring⟩ hmul
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left p hqr.le) hrs.le).trans
      (Nat.le_of_dvd hgpos hd)
  · have hmul := three_primes_mul_dvd q r s m hq hr hs
      (ne_of_lt hqr) (ne_of_lt hqs) (ne_of_lt hrs) h.1 h.2.1 h.2.2
    have hd : q * r * s ∣ Nat.gcd (p * q * r * s) m :=
      Nat.dvd_gcd ⟨p, by ring⟩ hmul
    exact (Nat.mul_le_mul (Nat.mul_le_mul hpq.le hqr.le) hrs.le).trans
      (Nat.le_of_dvd hgpos hd)

/-- The upper bound is attained at the largest prime index, independently of
the six pair exclusions.-/
theorem gcd_four_primes_at_largest (p q r s : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    Nat.gcd (p * q * r * s) ((p * q * r * s).choose s) = p * q * r := by
  have hpr : p < r := lt_trans hpq hqr
  have hps : p < s := lt_trans hpr hrs
  have hqs : q < s := lt_trans hqr hrs
  have hpC : p ∣ (p * q * r * s).choose s :=
    dvd_choose_other_prime p s _ hp hs ⟨q * r * s, by ring⟩ (ne_of_lt hps)
  have hqC : q ∣ (p * q * r * s).choose s :=
    dvd_choose_other_prime q s _ hq hs ⟨p * r * s, by ring⟩ (ne_of_lt hqs)
  have hrC : r ∣ (p * q * r * s).choose s :=
    dvd_choose_other_prime r s _ hr hs ⟨p * q * s, by ring⟩ (ne_of_lt hrs)
  have hpqrC : p * q * r ∣ (p * q * r * s).choose s :=
    three_primes_mul_dvd p q r _ hp hq hr
      (ne_of_lt hpq) (ne_of_lt hpr) (ne_of_lt hqr) hpC hqC hrC
  have hsp : ¬ s ∣ p := fun hd =>
    (ne_of_gt hps) ((Nat.prime_dvd_prime_iff_eq hs hp).mp hd)
  have hsq : ¬ s ∣ q := fun hd =>
    (ne_of_gt hqs) ((Nat.prime_dvd_prime_iff_eq hs hq).mp hd)
  have hsr : ¬ s ∣ r := fun hd =>
    (ne_of_gt hrs) ((Nat.prime_dvd_prime_iff_eq hs hr).mp hd)
  have hsN : ¬ s ∣ (p * q * r * s) / s := by
    rw [Nat.mul_div_cancel _ hs.pos]
    exact hs.not_dvd_mul (hs.not_dvd_mul hsp hsq) hsr
  have hsC : ¬ s ∣ (p * q * r * s).choose s :=
    not_dvd_choose_prime s _ hs hsN
  calc
    Nat.gcd (p * q * r * s) ((p * q * r * s).choose s) =
        Nat.gcd (s * (p * q * r)) ((p * q * r * s).choose s) := by
      congr 1
      ring
    _ = p * q * r := Nat.gcd_mul_of_coprime_of_dvd
      (hs.coprime_iff_not_dvd.mpr hsC) hpqrC

/-- The prime index used above belongs to the minimization range.-/
theorem largest_prime_in_range (p q r s : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) :
    1 < s ∧ s ≤ (p * q * r * s) / 2 := by
  have hpqr : 2 ≤ p * q * r :=
    hp.two_le.trans ((Nat.le_mul_of_pos_right p hq.pos).trans
      (Nat.le_mul_of_pos_right (p * q) hr.pos))
  refine ⟨hs.one_lt, (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr ?_⟩
  calc
    s * 2 = 2 * s := mul_comm _ _
    _ ≤ p * q * r * s := Nat.mul_le_mul_right s hpqr

/-- Abstract minimum theorem: only the three-of-four divisibility assertion
remains to be supplied by a concrete prime configuration.-/
theorem f_four_primes_of_threeOfFour (p q r s : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hSupport : ∀ k : ℕ, 1 < k → k ≤ (p * q * r * s) / 2 →
      ThreeOfFour p q r s ((p * q * r * s).choose k)) :
    f (p * q * r * s) = p * q * r := by
  have hsrange := largest_prime_in_range p q r s hp hq hr hs
  have hwitness := gcd_four_primes_at_largest p q r s hp hq hr hs hpq hqr hrs
  have hmem : p * q * r ∈ {m | ∃ k, 1 < k ∧ k ≤ (p * q * r * s) / 2 ∧
      m = Nat.gcd (p * q * r * s) ((p * q * r * s).choose k)} :=
    ⟨s, hsrange.1, hsrange.2, hwitness.symm⟩
  apply Nat.le_antisymm
  · exact Nat.sInf_le hmem
  · have hmin := Nat.sInf_mem ⟨p * q * r, hmem⟩
    obtain ⟨k, hk1, hk2, hkEq⟩ := hmin
    change f (p * q * r * s) = _ at hkEq
    rw [hkEq]
    exact gcd_four_primes_ge_of_threeOfFour p q r s _ hp hq hr hs hpq hqr hrs
      (hSupport k hk1 hk2)

/-- Final framework with the six exclusions as its sole binomial hypothesis.-/
theorem f_four_primes_of_noTwoMissing (p q r s : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hPairs : ∀ k : ℕ, 1 < k → k ≤ (p * q * r * s) / 2 →
      NoTwoMissing p q r s ((p * q * r * s).choose k)) :
    f (p * q * r * s) = p * q * r := by
  apply f_four_primes_of_threeOfFour p q r s hp hq hr hs hpq hqr hrs
  intro k hk1 hk2
  exact threeOfFour_of_noTwoMissing p q r s _ (hPairs k hk1 hk2)

/-- A version with an explicitly named product `N`.-/
theorem f_eq_three_prime_product (N p q r s : ℕ)
    (hN : N = p * q * r * s)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hPairs : ∀ k : ℕ, 1 < k → k ≤ N / 2 →
      NoTwoMissing p q r s (N.choose k)) :
    f N = p * q * r := by
  subst N
  exact f_four_primes_of_noTwoMissing p q r s hp hq hr hs hpq hqr hrs hPairs

end Erdos700
