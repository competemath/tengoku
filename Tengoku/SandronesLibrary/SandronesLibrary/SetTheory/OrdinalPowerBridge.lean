/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Ordinal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / OrdinalPowerBridge —— 本库序数幂与 mathlib 序数幂的桥

Goodstein 的遗传底数表达式使用本库的 `ordinalPow`。不管是比较两个
`omega`—幂，还是调用 mathlib 中已经证明的 Cantor 项引理，都需要一条
公开而精确的运算对应。本文件只提供这条对应及其直接的指数比较接口。
-/

namespace SandronesLibrary.SetTheory.Ordinal

noncomputable section

universe u

end

end SandronesLibrary.SetTheory.Ordinal
