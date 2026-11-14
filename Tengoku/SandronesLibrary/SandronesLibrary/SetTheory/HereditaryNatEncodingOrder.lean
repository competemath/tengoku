/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HereditaryNatEncoding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Order interface for the corrected hereditary encoder -/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

private theorem ordinalPow_omega_one :
    ordinalPow Ordinal.omega0 ((1 : ℕ) : Ordinal) = Ordinal.omega0 := by
  change ordinalPow Ordinal.omega0 (Order.succ 0) = Ordinal.omega0
  rw [ordinalPow_succ, ordinalPow_zero]
  simp [ordinalMul]

theorem hereditaryNatEncode_omega_equation (base : ℕ) (hbase : 2 ≤ base) (n : ℕ) :
    (hereditaryNatEncode base hbase n).omegaValue =
      Ordinal.omega0 * (hereditaryNatEncode base hbase (n / base)).omegaValue +
        (n % base : ℕ) := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp [hereditaryNatEncode_zero, HereditaryBaseExpr.omegaValue]
  · rw [hereditaryNatEncode_of_pos base hbase hn]
    simp only [HereditaryBaseExpr.omegaValue, ordinalPow_omega_one]
    rw [show ordinalMul Ordinal.omega0
          (hereditaryNatEncode base hbase (n / base)).omegaValue =
          Ordinal.omega0 * (hereditaryNatEncode base hbase (n / base)).omegaValue by
          simp [ordinalMul],
      show ordinalAdd
          (Ordinal.omega0 * (hereditaryNatEncode base hbase (n / base)).omegaValue)
          (n % base : ℕ) =
          Ordinal.omega0 * (hereditaryNatEncode base hbase (n / base)).omegaValue +
            (n % base : ℕ) by simp [ordinalAdd]]

/--
> **Entry**: settheory.googology.hereditary-natural-encoding-same-block-order
> **一句话**: 修正后的编码在商相同的同一底数块内严格保序，并具有 `ω·商序数+余数` 的精确方程。
> **依赖**: `settheory.googology.hereditary-natural-encoding`
> **mathlib**: `add_lt_add_iff_left`、`Nat.div_add_mod`-/
theorem hereditaryNatEncode_omega_lt_of_div_eq {base : ℕ} (hbase : 2 ≤ base)
    {n m : ℕ} (hnm : n < m) (hdiv : n / base = m / base) :
    (hereditaryNatEncode base hbase n).omegaValue <
      (hereditaryNatEncode base hbase m).omegaValue := by
  have hnEq := hereditaryNatEncode_omega_equation base hbase n
  have hmEq := hereditaryNatEncode_omega_equation base hbase m
  rw [hnEq, hmEq, hdiv]
  apply (add_lt_add_iff_left _).2
  have hnrepr : base * (n / base) + n % base = n := by
    exact Nat.div_add_mod n base
  have hmrepr : base * (m / base) + m % base = m := by
    exact Nat.div_add_mod m base
  rw [hdiv] at hnrepr
  have hmod : n % base < m % base := by omega
  exact_mod_cast hmod

private theorem omega_blocks_strictly_separated {a b : Ordinal} {r s : ℕ}
    (hab : a < b) :
    Ordinal.omega0 * a + (r : Ordinal) <
      Ordinal.omega0 * b + (s : Ordinal) := by
  have hr : (r : Ordinal) < Ordinal.omega0 :=
    Ordinal.natCast_lt_omega0 r
  have hwithin : Ordinal.omega0 * a + (r : Ordinal) <
      Ordinal.omega0 * a + Ordinal.omega0 :=
    (add_lt_add_iff_left (Ordinal.omega0 * a)).2 hr
  rw [← Ordinal.mul_succ] at hwithin
  have hblocks : Ordinal.omega0 * Order.succ a ≤
      Ordinal.omega0 * b :=
    mul_le_mul_right (Order.succ_le_iff.mpr hab) Ordinal.omega0
  exact hwithin.trans_le (hblocks.trans le_self_add)

/--
> **Entry**: settheory.googology.hereditary-natural-encoding-strict-order
> **一句话**: 修正 Horner 乘法方向后，固定底数的遗传自然数编码在 `omegaValue` 下全局严格保序。
> **依赖**: `settheory.googology.hereditary-natural-encoding-same-block-order`
> **mathlib**: `Ordinal.mul_succ`、`Ordinal.natCast_lt_omega0`-/
theorem hereditaryNatEncode_omega_strictMono (base : ℕ) (hbase : 2 ≤ base) :
    StrictMono (fun n ↦ (hereditaryNatEncode base hbase n).omegaValue) := by
  intro n m hnm
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
      by_cases hdiv : n / base = m / base
      · exact hereditaryNatEncode_omega_lt_of_div_eq hbase hnm hdiv
      · have hquot_le : n / base ≤ m / base :=
          Nat.div_le_div_right hnm.le
        have hquot_lt : n / base < m / base :=
          lt_of_le_of_ne hquot_le hdiv
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
        have hsmaller : m / base < m :=
          Nat.div_lt_self hmpos (lt_of_lt_of_le Nat.one_lt_two hbase)
        have hrecursive := ih (m / base) hsmaller hquot_lt
        change (hereditaryNatEncode base hbase n).omegaValue <
          (hereditaryNatEncode base hbase m).omegaValue
        have hnEq := hereditaryNatEncode_omega_equation base hbase n
        have hmEq := hereditaryNatEncode_omega_equation base hbase m
        rw [hnEq, hmEq]
        exact omega_blocks_strictly_separated hrecursive

end
end SandronesLibrary.SetTheory.Googology
