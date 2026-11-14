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

/-- The textbook finite count agrees with Mathlib's arithmetic totient function.
@isnad1 id=eq.0h1v.s3.7ff53859b4cd from=translated src=- shape=0fc427d2 vocab=83e87805
-/
theorem eulerTotient_eq_natTotient (n : ℕ) : EulerTotient n = n.totient := by
  simp [EulerTotient, Nat.totient, Nat.coprime_comm]

/-- `φ(n)` 等于剩余环 `ZMod n` 的单位数。
> **Entry**: number-theory.elementary.totient
@isnad1 id=eq.0h1v.s5.9d4ad2daf82c from=translated src=- shape=f255912d vocab=ef2d22c2
-/
theorem reduced_residue_card (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = n.totient := by
  exact ZMod.card_units_eq_totient n

/-- The unit group of `ZMod n` has cardinality equal to the textbook Euler totient.
@isnad1 id=eq.0h1v.s5.ddfda571a86d from=translated src=- shape=f255912d vocab=d8cf2baa
-/
theorem reduced_residue_card_eulerTotient (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = EulerTotient n := by
  rw [eulerTotient_eq_natTotient]
  exact reduced_residue_card n

/-- **Euler 定理**：若 `a,n` 互素，则 `a ^ φ(n) ≡ 1 (mod n)`。
> **Entry**: number-theory.elementary.fermat-euler
@isnad1 id=modeq.1h2v.s4.03c1123c2ad8 from=translated src=- shape=f467a28d vocab=108cea45
-/
theorem euler_theorem {a n : ℕ} (h : a.Coprime n) :
    a ^ n.totient ≡ 1 [MOD n] := by
  exact Nat.ModEq.pow_totient h

/-- Euler's theorem stated using the textbook totient and congruence definitions.
@isnad1 id=congruen.1h2v.s4.f9d972c3f5d5 from=translated src=- shape=f467a28d vocab=e84881e3
-/
theorem euler_theorem_congruent {a n : ℕ} (h : a.Coprime n) :
    Congruent n (a ^ EulerTotient n) 1 := by
  rw [eulerTotient_eq_natTotient, congruent_iff_modEq]
  exact euler_theorem h

/-- **Fermat 小定理（既约形式）**：素数 `p` 不整除 `a` 时，`a^(p-1) ≡ 1 (mod p)`。
> **Entry**: number-theory.elementary.fermat-euler
@isnad1 id=modeq.2h2v.s5.0688e9f70af4 from=translated src=- shape=69b6115d vocab=024de6c0
-/
theorem fermat_little_theorem_of_not_dvd {a p : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have hcop : a.Coprime p := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpa)
  simpa [Nat.totient_prime hp] using euler_theorem hcop

/-- **Fermat 小定理（无条件形式）**：对任意自然数 `a`，都有 `a^p ≡ a (mod p)`。
> **Entry**: number-theory.elementary.fermat-euler
@isnad1 id=modeq.1h2v.s4.c70bb22bc685 from=translated src=- shape=99ffe830 vocab=285a6070
-/
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
