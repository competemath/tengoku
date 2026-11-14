/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HereditaryNatEncodingOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact ordinal rank of encoded base powers -/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

private theorem ordinalMul_eq_native (a b : Ordinal) :
    ordinalMul a b = a * b := by
  simp [ordinalMul]

private theorem omega_mul_ordinalPow_omega_nat (k : ℕ) :
    Ordinal.omega0 * ordinalPow Ordinal.omega0 (k : Ordinal) =
      ordinalPow Ordinal.omega0 ((k + 1 : ℕ) : Ordinal) := by
  induction k with
  | zero =>
      rw [show ((0 + 1 : ℕ) : Ordinal) = Order.succ 0 by norm_num,
        ordinalPow_succ, ordinalPow_zero]
      simp [ordinalMul]
  | succ k ih =>
      norm_num only [Nat.cast_succ]
      simp only [← Order.succ_eq_add_one]
      rw [ordinalPow_succ, ordinalPow_succ]
      rw [ordinalMul_eq_native, ordinalMul_eq_native]
      rw [← mul_assoc, ih]
      congr 2

private theorem nat_pow_succ_div_self (q k : ℕ) (hq : 2 ≤ q) :
    q ^ (k + 1) / q = q ^ k := by
  rw [pow_succ]
  exact Nat.mul_div_left _ (by omega)

private theorem nat_pow_succ_mod_self (q k : ℕ) (_hq : 2 ≤ q) :
    q ^ (k + 1) % q = 0 := by
  rw [pow_succ, Nat.mul_mod_left]

/--
> **Entry**: settheory.googology.hereditary-natural-power-rank
> **一句话**: 底数 `q≥2` 时，`q^k` 的修正遗传编码在 `omegaValue` 下精确等于本库的 `ω^k`。
> **依赖**: `settheory.googology.hereditary-natural-encoding-strict-order`
> **mathlib**: `Nat.mul_div_left`、`Nat.mul_mod_left`-/
theorem hereditaryNatEncode_power_omegaValue (q : ℕ) (hq : 2 ≤ q) :
    ∀ k : ℕ,
      (hereditaryNatEncode q hq (q ^ k)).omegaValue =
        ordinalPow Ordinal.omega0 (k : Ordinal) := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero, hereditaryNatEncode_omega_equation]
      have hone : 1 < q := lt_of_lt_of_le Nat.one_lt_two hq
      rw [Nat.div_eq_of_lt hone, Nat.mod_eq_of_lt hone,
        hereditaryNatEncode_zero]
      simp [HereditaryBaseExpr.omegaValue, ordinalPow_zero]
  | succ k ih =>
      rw [hereditaryNatEncode_omega_equation,
        show q ^ (k + 1) / q = q ^ k from nat_pow_succ_div_self q k hq,
        show q ^ (k + 1) % q = 0 from nat_pow_succ_mod_self q k hq,
        ih]
      simpa using omega_mul_ordinalPow_omega_nat k

/-- Every encoded natural below `q^k` has ordinal value strictly below the exact rank `ω^k`.-/
theorem hereditaryNatEncode_lt_power_omegaValue {q k n : ℕ} (hq : 2 ≤ q)
    (hn : n < q ^ k) :
    (hereditaryNatEncode q hq n).omegaValue <
      ordinalPow Ordinal.omega0 (k : Ordinal) := by
  rw [← hereditaryNatEncode_power_omegaValue q hq k]
  exact hereditaryNatEncode_omega_strictMono q hq hn

end
end SandronesLibrary.SetTheory.Googology
