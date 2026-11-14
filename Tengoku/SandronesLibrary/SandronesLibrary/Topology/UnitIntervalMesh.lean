/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Topology.UnitInterval
import Tengoku.Seed.Topology.MetricSpace.Pseudo.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 单位区间的一致有限网格

本文件建立只依赖单位区间度量结构的一致有限网格：正整数 `N` 对应网格点 `i / N`，首末点为
`0`、`1`，相邻点单调且距离恰为 `N⁻¹`。这些接口同时供道路细分、方格细分和折线逼近使用，
不属于 van Kampen 专用理论。

当前条目：

* `topology.homotopy.unit-interval-mesh`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

/-- 把单位区间等分成 `N` 段时的第 `i` 个网格点 `i / N`。

> **Entry**: topology.homotopy.unit-interval-mesh-/
def unitIntervalMeshPoint (N : ℕ) (hN : 0 < N)
    (i : Fin (N + 1)) : unitInterval :=
  ⟨(i : ℝ) / (N : ℝ), by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · apply (div_le_one (by exact_mod_cast hN)).2
      exact_mod_cast Nat.le_of_lt_succ i.isLt⟩

/--
@isnad1 id=eq.1h1v.s6.d5be14baf80f from=translated src=- shape=17135129 vocab=2b7098a2
-/
@[simp] theorem unitIntervalMeshPoint_zero (N : ℕ) (hN : 0 < N) :
    unitIntervalMeshPoint N hN 0 = 0 := by
  ext
  simp [unitIntervalMeshPoint]

/--
@isnad1 id=eq.1h1v.s5.754c0e887728 from=translated src=- shape=4a730efe vocab=0f6839d2
-/
@[simp] theorem unitIntervalMeshPoint_last (N : ℕ) (hN : 0 < N) :
    unitIntervalMeshPoint N hN (Fin.last N) = 1 := by
  ext
  simp [unitIntervalMeshPoint, ne_of_gt hN]

/--
@isnad1 id=le.1h2v.s5.02ba2d0b531d from=translated src=- shape=3c9ccf49 vocab=4c7a6820
-/
theorem unitIntervalMeshPoint_castSucc_le_succ
    (N : ℕ) (hN : 0 < N) (i : Fin N) :
    unitIntervalMeshPoint N hN i.castSucc ≤ unitIntervalMeshPoint N hN i.succ := by
  change (i : ℝ) / (N : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) / (N : ℝ)
  gcongr
  exact_mod_cast Nat.le_succ i.val

/--
@isnad1 id=eq.1h2v.s5.2457ff6444ca from=translated src=- shape=b4c22d68 vocab=2a3881a6
-/
theorem dist_unitIntervalMeshPoint_castSucc_succ
    (N : ℕ) (hN : 0 < N) (i : Fin N) :
    dist (unitIntervalMeshPoint N hN i.castSucc)
      (unitIntervalMeshPoint N hN i.succ) = (N : ℝ)⁻¹ := by
  rw [Subtype.dist_eq, Real.dist_eq]
  change |(i.val : ℝ) / (N : ℝ) - ((i.val + 1 : ℕ) : ℝ) / (N : ℝ)| = (N : ℝ)⁻¹
  rw [Nat.cast_add, Nat.cast_one]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  rw [show (i : ℝ) / (N : ℝ) - ((i : ℝ) + 1) / (N : ℝ) = -(N : ℝ)⁻¹ by
    field_simp
    ring]
  rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]

end SandronesLibrary.Topology
