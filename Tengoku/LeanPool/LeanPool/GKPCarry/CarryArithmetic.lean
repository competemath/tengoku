/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.GKPCarry.Definitions
public import Tengoku.LeanPool.LeanPool.GKPCarry.Statement
import Tengoku.LeanPool.LeanPool.GKPCarry.BinaryReduction
import Tengoku.LeanPool.LeanPool.GKPCarry.Kummer
public import Tengoku

/-!
# Arithmetic correctness of the ternary doubling transducer

The transducer in `GKPCarry.Definitions` counts outgoing carries while doubling
a little-endian ternary word.  This file proves that, on the canonical ternary
digits of `n`, twice that count is exactly Kummer's ternary digit excess.
-/

@[expose] public section

namespace GKPCarry

open Nat

/-- Kummer's ternary digit excess for a central binomial coefficient. -/
def ternaryDigitExcess (n : ℕ) : ℕ :=
  2 * (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n)).sum

/-- Fixed-length output digits emitted while doubling a ternary word.  The
final carry is retained as the last digit. -/
def ternaryDoubleDigitsAux : List ℕ → ℕ → List ℕ
  | [], carry => [carry]
  | digit :: digits, carry =>
      ((2 * digit + carry) % 3) ::
        ternaryDoubleDigitsAux digits (ternaryDoubleCarryStep carry digit)

/--
@isnad1 id=le.0h2v.s3.c06c8ee6d365 from=translated src=- shape=aa052b1b vocab=45f1fbae
-/
lemma ternaryDoubleCarryStep_le_one (carry digit : ℕ) :
    ternaryDoubleCarryStep carry digit ≤ 1 := by
  unfold ternaryDoubleCarryStep
  split <;> omega

/--
@isnad1 id=lt.0h2v.s3.bca8cec9d274 from=translated src=- shape=aa052b1b vocab=cd45d243
-/
lemma ternaryDoubleCarryStep_lt_three (carry digit : ℕ) :
    ternaryDoubleCarryStep carry digit < 3 := by
  have := ternaryDoubleCarryStep_le_one carry digit
  omega

/--
@isnad1 id=eq.2h2v.s5.a79f4571877a from=translated src=- shape=6f2b1486 vocab=a5bd7448
-/
lemma ternaryDoubleCarryStep_eq_div
    {carry digit : ℕ} (hcarry : carry ≤ 1) (hdigit : digit < 3) :
    ternaryDoubleCarryStep carry digit = (2 * digit + carry) / 3 := by
  interval_cases digit <;> interval_cases carry <;> decide

/--
@isnad1 id=eq.2h2v.s6.6e164b24ba66 from=translated src=- shape=0288d42c vocab=6b4bcab1
-/
lemma ternaryDoubleCarryStep_local
    {carry digit : ℕ} (hcarry : carry ≤ 1) (hdigit : digit < 3) :
    (2 * digit + carry) % 3 + 3 * ternaryDoubleCarryStep carry digit =
      2 * digit + carry := by
  rw [ternaryDoubleCarryStep_eq_div hcarry hdigit]
  exact Nat.mod_add_div (2 * digit + carry) 3

/--
@isnad1 id=eq.0h2v.s4.bd43d212b263 from=translated src=- shape=0f54dc46 vocab=dac64b88
-/
lemma ternaryDoubleDigitsAux_length (digits : List ℕ) (carry : ℕ) :
    (ternaryDoubleDigitsAux digits carry).length = digits.length + 1 := by
  induction digits generalizing carry with
  | nil => simp [ternaryDoubleDigitsAux]
  | cons digit digits ih => simp [ternaryDoubleDigitsAux, ih, Nat.add_assoc]

/--
@isnad1 id=lt.3h3v.s5.b5c3e15091f8 from=translated src=- shape=77436845 vocab=773a60e9
-/
lemma ternaryDoubleDigitsAux_lt_three
    {digits : List ℕ} {carry : ℕ} (hcarry : carry < 3)
    (hdigits : ∀ digit ∈ digits, digit < 3) :
    ∀ value ∈ ternaryDoubleDigitsAux digits carry, value < 3 := by
  induction digits generalizing carry with
  | nil => simpa [ternaryDoubleDigitsAux]
  | cons digit digits ih =>
      intro value hvalue
      rw [ternaryDoubleDigitsAux] at hvalue
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact Nat.mod_lt _ (by decide)
      · apply ih (ternaryDoubleCarryStep_lt_three carry digit)
          (fun d hd => hdigits d (List.mem_cons_of_mem digit hd))
          value htail

/--
@isnad1 id=eq.2h2v.s6.f702ac50e72c from=translated src=- shape=ac464746 vocab=ba8e7636
-/
lemma ternaryDoubleDigitsAux_ofDigits
    {digits : List ℕ} {carry : ℕ} (hcarry : carry ≤ 1)
    (hdigits : ∀ digit ∈ digits, digit < 3) :
    Nat.ofDigits 3 (ternaryDoubleDigitsAux digits carry) =
      2 * Nat.ofDigits 3 digits + carry := by
  induction digits generalizing carry with
  | nil => simp [ternaryDoubleDigitsAux, Nat.ofDigits]
  | cons digit digits ih =>
      have hdigit : digit < 3 := hdigits digit List.mem_cons_self
      have htail : ∀ d ∈ digits, d < 3 :=
        fun d hd => hdigits d (List.mem_cons_of_mem digit hd)
      have hnext := ternaryDoubleCarryStep_le_one carry digit
      have hlocal := ternaryDoubleCarryStep_local hcarry hdigit
      simp [ternaryDoubleDigitsAux, Nat.ofDigits, ih hnext htail]
      omega

/--
@isnad1 id=eq.2h2v.s6.acb9bc9ab214 from=translated src=- shape=c8d90a32 vocab=7b44efd0
-/
lemma ternaryDoubleDigitsAux_sum_add_two_mul_carries
    {digits : List ℕ} {carry : ℕ} (hcarry : carry ≤ 1)
    (hdigits : ∀ digit ∈ digits, digit < 3) :
    (ternaryDoubleDigitsAux digits carry).sum +
        2 * ternaryDoubleCarryCountAux digits carry =
      2 * digits.sum + carry := by
  induction digits generalizing carry with
  | nil => simp [ternaryDoubleDigitsAux, ternaryDoubleCarryCountAux]
  | cons digit digits ih =>
      have hdigit : digit < 3 := hdigits digit List.mem_cons_self
      have htail : ∀ d ∈ digits, d < 3 :=
        fun d hd => hdigits d (List.mem_cons_of_mem digit hd)
      have hnext := ternaryDoubleCarryStep_le_one carry digit
      have hlocal := ternaryDoubleCarryStep_local hcarry hdigit
      have hrec := ih hnext htail
      simp [ternaryDoubleDigitsAux, ternaryDoubleCarryCountAux]
      omega

/-- Headline carry identity: Kummer's ternary digit excess is exactly twice
the number of carries generated by ternary doubling.
@isnad1 id=eq.0h1v.s4.20b2bfe623ae from=translated src=- shape=e0f1d26b vocab=87159819
-/
theorem ternaryDigitExcess_eq_two_mul_ternaryDoubleCarryCount (n : ℕ) :
    ternaryDigitExcess n =
      2 * ternaryDoubleCarryCount (Nat.digits 3 n) := by
  let output := ternaryDoubleDigitsAux (Nat.digits 3 n) 0
  have hdigits : ∀ digit ∈ Nat.digits 3 n, digit < 3 :=
    fun digit hdigit => Nat.digits_lt_base (by decide) hdigit
  have hlength : output.length = (Nat.digits 3 n).length + 1 := by
    simpa [output] using ternaryDoubleDigitsAux_length (Nat.digits 3 n) 0
  have hvalid : ∀ digit ∈ output, digit < 3 := by
    simpa [output] using
      (ternaryDoubleDigitsAux_lt_three
        (digits := Nat.digits 3 n) (carry := 0) (by decide) hdigits)
  have hvalue : Nat.ofDigits 3 output = 2 * n := by
    calc
      Nat.ofDigits 3 output =
          2 * Nat.ofDigits 3 (Nat.digits 3 n) + 0 := by
            simpa [output] using
              (ternaryDoubleDigitsAux_ofDigits
                (digits := Nat.digits 3 n) (carry := 0) (by decide) hdigits)
      _ = 2 * n := by simp [Nat.ofDigits_digits]
  have hsum : (Nat.digits 3 (2 * n)).sum = output.sum := by
    calc
      (Nat.digits 3 (2 * n)).sum =
          (Nat.digits 3 (Nat.ofDigits 3 output)).sum := by rw [hvalue]
      _ = output.sum :=
        Nat.sum_digits_ofDigits_eq_sum (by decide) ⟨hlength, hvalid⟩
  have hcarry :
      output.sum + 2 * ternaryDoubleCarryCount (Nat.digits 3 n) =
        2 * (Nat.digits 3 n).sum := by
    simpa [output, ternaryDoubleCarryCount] using
      (ternaryDoubleDigitsAux_sum_add_two_mul_carries
        (digits := Nat.digits 3 n) (carry := 0) (by decide) hdigits)
  unfold ternaryDigitExcess
  rw [hsum]
  omega

/-- Two ternary doubling carries imply divisibility of the central binomial
coefficient by nine.
@isnad1 id=dvd.1h1v.s4.9c320040e0cd from=translated src=- shape=7efe08aa vocab=86e27751
-/
theorem nine_dvd_centralBinom_of_two_le_ternaryDoubleCarryCount
    {n : ℕ} (h : 2 ≤ ternaryDoubleCarryCount (Nat.digits 3 n)) :
    9 ∣ Nat.centralBinom n := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hexcess : 4 ≤ ternaryDigitExcess n := by
    rw [ternaryDigitExcess_eq_two_mul_ternaryDoubleCarryCount]
    omega
  have hbound : (3 - 1) * 2 ≤
      2 * (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n)).sum := by
    simpa [ternaryDigitExcess] using hexcess
  simpa using
    (pow_dvd_centralBinom_of_digit_excess (p := 3) (n := n) (e := 2) hbound)

/-- A universal carry certificate on nonexceptional powers of two would imply
the GKP conjecture.
@isnad1 id=gkpconje.1h0v.s6.2c37797ab5ac from=translated src=- shape=0935aad1 vocab=b2b7f027
-/
theorem gkpConjecture_of_ternaryCarryCount
    (h : ∀ k : ℕ, 2 < k → k ≠ 6 → k ≠ 8 →
      2 ≤ ternaryDoubleCarryCount (Nat.digits 3 (2 ^ k))) :
    gkpConjecture := by
  apply gkpConjecture_of_powerOfTwo
  intro k hk2 hk6 hk8
  exact nine_dvd_centralBinom_of_two_le_ternaryDoubleCarryCount
    (h k hk2 hk6 hk8)

end GKPCarry
