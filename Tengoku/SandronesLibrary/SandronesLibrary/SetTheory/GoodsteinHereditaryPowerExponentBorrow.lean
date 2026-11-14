/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HereditaryNatPowerRank
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.OrdinalPowerBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 遗传指数族 `B^(B^k)` 的 Goodstein 借位

本文件处理 `head + B^(B^k)` 的换底减一步，其中 `k` 是正的合法数字。新数值
`q^(q^k)-1` 不再靠有限位数的手工借位展开，而是交给一般遗传自然数编码器重新编码。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/--
> **Entry**: settheory.googology.goodstein-hereditary-power-exponent-borrow
> **一句话**: 正数字 `k` 的参数族 `head+B^(B^k)` 在升底减一并完全重编码后，数值正确且 `ω` 度量严格下降。
> **依赖**: `settheory.googology.hereditary-natural-power-rank`、
>   `settheory.ordinal.power-bridge`
> **mathlib**: `Ordinal.natCast_lt_omega0`、`Ordinal.opow_le_opow_right`

`head + B^(B^k)` 这一族表达式的带证书数据，其中 `k` 是正的合法数字。-/
structure HereditaryPowerExponentBorrowForm (base : ℕ) where
  base_ge_two : 2 ≤ base
  exponent : ℕ
  exponent_positive : 0 < exponent
  exponent_valid : exponent < base
  head : HereditaryBaseExpr
  head_valid : head.Valid base

end
end SandronesLibrary.SetTheory.Googology
