/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.CanonicalGoodsteinState

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # 一般换底重编码保持 `omegaValue`

`CanonicalGoodsteinState.lean` 把无条件一步序数下降所缺的正规化桥显式命名成
`CanonicalBaseChangeOmegaCompatible`，并注明它「尚未对所有规范状态得到证明」。本文件消解这条
命名义务：对任意底数 `2 ≤ b ≤ c` 和自然数 `n`，把 `n` 在底数 `b` 下的规范遗传编码放到新底数
`c` 下求值，再用 `c` 重新规范编码，所得表达式的 `omegaValue` 与原编码完全相同。

证明是对 `n` 的强归纳。正数情形两侧共用同一条商余方程：`b` 侧直接给出
`ω · omegaValue(编码 n/b) + n%b`，而 `c` 侧把换底求值后的数写成 `c · Q + n%b`（`Q` 是
`n/b` 的编码在 `c` 下的求值），于是商恰好回到 `Q`、余数仍是 `n%b`，归纳假设正好把 `Q` 那一项
换回 `b` 侧的商编码。

本文件**不**证明无条件的 Goodstein 单步下降，也**不**声称序列终止：它只补上换底正规化这一侧。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/-
引理清单：
1. `div_mul_add_div_eq`：`r < c → (c * Q + r) / c = Q`。
2. `div_mul_add_mod_eq`：`r < c → (c * Q + r) % c = r`。
3. `hereditaryNatEncode_baseChange_omegaValue`：主定理，对 `n` 强归纳；正数情形由
   `hereditaryNatEncode_of_pos` 展开求值，再用两侧 `hereditaryNatEncode_omega_equation` 对齐。
4. `canonicalBaseChangeReencoding_preserves`：把主定理实例到 `CanonicalGoodsteinState`，
   直接给出 `CanonicalBaseChangeOmegaCompatible`。
-/

/-- 商余分解的除法一侧：余数已经小于底数时，`c * Q + r` 除以 `c` 精确回到 `Q`。-/
private theorem div_mul_add_div_eq (c Q r : ℕ) (hc : 0 < c) (hr : r < c) :
    (c * Q + r) / c = Q := by
  rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hr, Nat.add_zero]

/-- 商余分解的取余一侧：余数已经小于底数时，`c * Q + r` 模 `c` 仍是 `r`。-/
private theorem div_mul_add_mod_eq (c Q r : ℕ) (hr : r < c) :
    (c * Q + r) % c = r := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/--
> **Entry**: settheory.googology.hereditary-encoding-order
> **一句话**: 对任意 `2 ≤ b ≤ c` 与自然数 `n`，把 `b` 下的规范遗传编码在 `c` 下求值后再用 `c`
> 重新编码，所得表达式的 `omegaValue` 与原来完全相同。
> **依赖**: `settheory.googology.canonical-goodstein-state`、
> `settheory.googology.hereditary-natural-encoding`、
> `settheory.googology.hereditary-natural-encoding-same-block-order`
> **mathlib**: `Nat.mul_add_div`、`Nat.mul_add_mod`、`Nat.div_eq_of_lt`、`Nat.mod_eq_of_lt`

这是换底正规化的普适桥：编码只依赖底数与数值，而把旧树放到更高底数下重新读取数值、再重新编码，
不会改变它在 `ω` 处的序数解释。证明对 `n` 强归纳，正数情形把新底数下的求值写成 `c * Q + n%b`，
于是重编码的商余方程与旧底数的商余方程逐项对齐。
@isnad1 id=eq.2h3v.s5.fdc7c5f85af6 from=translated src=- shape=244bc91a vocab=f1d777df
-/
theorem hereditaryNatEncode_baseChange_omegaValue {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c)
    (n : ℕ) :
    (hereditaryNatEncode c (le_trans hb hbc) ((hereditaryNatEncode b hb n).eval c)).omegaValue =
      (hereditaryNatEncode b hb n).omegaValue := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain rfl | hn := n.eq_zero_or_pos
      · simp [hereditaryNatEncode_zero, HereditaryBaseExpr.eval, HereditaryBaseExpr.omegaValue]
      · have hbpos : 0 < b := by omega
        have hcpos : 0 < c := by omega
        have hmodc : n % b < c := lt_of_lt_of_le (Nat.mod_lt n hbpos) hbc
        have hdiv_lt : n / b < n := Nat.div_lt_self hn (by omega)
        have ihq := ih (n / b) hdiv_lt
        have hEval : (hereditaryNatEncode b hb n).eval c =
            c * (hereditaryNatEncode b hb (n / b)).eval c + n % b := by
          rw [hereditaryNatEncode_of_pos b hb hn]
          simp [HereditaryBaseExpr.eval, pow_one]
        rw [hEval,
          hereditaryNatEncode_omega_equation c (le_trans hb hbc)
            (c * (hereditaryNatEncode b hb (n / b)).eval c + n % b),
          hereditaryNatEncode_omega_equation b hb n,
          div_mul_add_div_eq c _ (n % b) hcpos hmodc,
          div_mul_add_mod_eq c _ (n % b) hmodc,
          ihq]

/-- `CanonicalGoodsteinState.lean` 命名的换底兼容义务现在无条件成立：规范状态在后继底数下
重新编码旧树的求值，所得序数度量与旧度量相同。
@isnad1 id=canonica.0h1v.s2.4fb3f8c688e4 from=translated src=- shape=5c11bb93 vocab=00b2f5a4
-/
theorem canonicalBaseChangeReencoding_preserves (s : CanonicalGoodsteinState) :
    CanonicalBaseChangeOmegaCompatible s := by
  simpa only [CanonicalBaseChangeOmegaCompatible, CanonicalGoodsteinState.baseChangeReencodingMeasure,
    CanonicalGoodsteinState.ordinalMeasure, CanonicalGoodsteinState.expression]
    using hereditaryNatEncode_baseChange_omegaValue (b := s.base) (c := s.base + 1)
      s.base_ge_two (Nat.le_succ s.base) s.value

end
end SandronesLibrary.SetTheory.Googology
