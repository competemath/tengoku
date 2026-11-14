/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.Congruence
import Tengoku.Seed.Data.Nat.Totient
import Tengoku.Seed.NumberTheory.PowModTotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Euler φ 函数与 Fermat–Euler 定理

Euler φ 函数计数模 `n` 的可逆剩余类。由有限单位群中元素的幂性质得到 Euler 定理，
再把模数专门化为素数，依次推出 Fermat 小定理的既约形式与无条件形式。
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- Euler's totient counts the natural numbers below `n` which are coprime to `n`.

> **Entry**: number-theory.elementary.totient-/
def EulerTotient (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun a ↦ a.Coprime n).card

/-- The textbook finite count agrees with Mathlib's arithmetic totient function.-/
theorem eulerTotient_eq_natTotient (n : ℕ) : EulerTotient n = n.totient := by
  simp [EulerTotient, Nat.totient, Nat.coprime_comm]

/-- `φ(n)` 等于剩余环 `ZMod n` 的单位数。
> **Entry**: number-theory.elementary.totient-/
theorem reduced_residue_card (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = n.totient := by
  exact ZMod.card_units_eq_totient n

/-- The unit group of `ZMod n` has cardinality equal to the textbook Euler totient.-/
theorem reduced_residue_card_eulerTotient (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = EulerTotient n := by
  rw [eulerTotient_eq_natTotient]
  exact reduced_residue_card n

/-- **Euler 定理**：若 `a,n` 互素，则 `a ^ φ(n) ≡ 1 (mod n)`。
> **Entry**: number-theory.elementary.fermat-euler-/
theorem euler_theorem {a n : ℕ} (h : a.Coprime n) :
    a ^ n.totient ≡ 1 [MOD n] := by
  exact Nat.ModEq.pow_totient h

/-- Euler's theorem stated using the textbook totient and congruence definitions.-/
theorem euler_theorem_congruent {a n : ℕ} (h : a.Coprime n) :
    Congruent n (a ^ EulerTotient n) 1 := by
  rw [eulerTotient_eq_natTotient, congruent_iff_modEq]
  exact euler_theorem h

/-- **Fermat 小定理（既约形式）**：素数 `p` 不整除 `a` 时，`a^(p-1) ≡ 1 (mod p)`。
> **Entry**: number-theory.elementary.fermat-euler-/
theorem fermat_little_theorem_of_not_dvd {a p : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have hcop : a.Coprime p := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpa)
  simpa [Nat.totient_prime hp] using euler_theorem hcop

/-- **Fermat 小定理（无条件形式）**：对任意自然数 `a`，都有 `a^p ≡ a (mod p)`。
> **Entry**: number-theory.elementary.fermat-euler-/
theorem fermat_little_theorem (a : ℕ) {p : ℕ} (hp : p.Prime) :
    a ^ p ≡ a [MOD p] := by
  by_cases hpa : p ∣ a
  · have ha0 : a ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpa
    have h0a : 0 ^ p ≡ a [MOD p] := by
      simpa [zero_pow hp.ne_zero] using ha0.symm
    exact (ha0.pow p).trans h0a
  · have h := (fermat_little_theorem_of_not_dvd hp hpa).mul_right a
    simpa [← pow_succ, Nat.sub_add_cancel hp.one_le] using h

end SandronesLibrary.NumberTheory.Elementary
