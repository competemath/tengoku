/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Metric
import Tengoku.Seed.Analysis.Normed.Module.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 赋范空间与 Banach 空间

范数把线性结构与度量结构连接起来。对向量 `x`，数 `‖x‖` 表示其大小；两点距离
由 `dist x y = ‖x-y‖` 给出。因此范数收敛与度量拓扑收敛一致，范数 Cauchy 条件
也正是度量 Cauchy 条件。

本模块补上此前位于 `Topology/Metric.lean` 与 `Lᵖ` 理论之间缺失的教材层：

* `NormedLinearSpace` 是 Mathlib `NormedSpace` 的教材别名；
* `BanachSpace` 表示实赋范线性空间的底层度量是完备的；
* 随后给出范数公理、反三角不等式、数乘相容性，以及收敛和 Cauchy 的范数判据。

这里不重复制造一套与 Mathlib 不兼容的结构。Mathlib 的 `NormedAddCommGroup` 已经
同时携带范数、加法群和范数诱导的度量；`NormedSpace 𝕜 E` 再表达标量数乘与范数
相容。后续 `Lᵖ`、内积空间和泛函分析可直接复用这些实例。
-/

namespace SandronesLibrary.Topology.NormedSpace

open Filter

/-- **赋范线性空间**：标量域 `𝕜` 上带有相容范数的向量空间。

该别名保留 Mathlib 的类型类结构，使所有连续性、度量与线性运算定理可直接使用。

> **Entry**: topology.normed-space.def-/
abbrev NormedLinearSpace (𝕜 E : Type*) [NormedField 𝕜]
    [NormedAddCommGroup E] := _root_.NormedSpace 𝕜 E

/-- **实 Banach 空间**：底层范数度量完备的实赋范线性空间。

使用时还需同时提供 `[NormedAddCommGroup E]` 与 `[NormedLinearSpace ℝ E]`；本别名
只命名额外的完备性条件。-/
abbrev BanachSpace (E : Type*) [NormedAddCommGroup E]
    [NormedLinearSpace ℝ E] := CompleteSpace E

variable {E : Type*} [NormedAddCommGroup E]

/-- 范数诱导距离：两点距离等于其差的范数。
@isnad1 id=eq.0h3v.s5.8c8c219bf0bb from=translated src=- shape=666cb7b9 vocab=2734acac
-/
theorem dist_eq_norm_sub [_normedLinear : NormedLinearSpace ℝ E] (x y : E) :
    dist x y = ‖x - y‖ := by
  exact dist_eq_norm x y

/-- 范数非负。
@isnad1 id=le.0h2v.s4.4ec928db0857 from=translated src=- shape=f9172607 vocab=b1b561c9
-/
theorem norm_nonnegative [_normedLinear : NormedLinearSpace ℝ E] (x : E) : 0 ≤ ‖x‖ := by
  exact norm_nonneg x

/-- 在真正的范数空间中，范数为零当且仅当向量为零。
@isnad1 id=iff.0h2v.s5.36e3cd4390f9 from=translated src=- shape=8eba36fb vocab=6a9c8d5a
-/
theorem norm_eq_zero_iff [_normedLinear : NormedLinearSpace ℝ E]
    {x : E} : ‖x‖ = 0 ↔ x = 0 := by
  exact norm_eq_zero

/-- **范数三角不等式**：和的范数不超过范数之和。

> **Entry**: topology.normed-space.inequalities
@isnad1 id=le.0h3v.s5.8aa13672a472 from=translated src=- shape=72084abc vocab=6a1be2fe
-/
theorem norm_triangle [_normedLinear : NormedLinearSpace ℝ E] (x y : E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  exact norm_add_le x y

/-- **反三角不等式**：范数函数关于自身诱导的距离是 `1`-Lipschitz 的。
@isnad1 id=le.0h3v.s5.0e7244bb35d4 from=translated src=- shape=2d8f40e7 vocab=ef235a91
-/
theorem reverse_triangle [_normedLinear : NormedLinearSpace ℝ E] (x y : E) :
    |‖x‖ - ‖y‖| ≤ ‖x - y‖ := by
  exact abs_norm_sub_norm_le x y

/-- 标量数乘与范数相容：`‖c • x‖ = ‖c‖ ‖x‖`。
@isnad1 id=eq.0h3v.s6.7b02efbc301e from=translated src=- shape=686733da vocab=fbc36dd2
-/
theorem norm_smul_eq [_normedLinear : NormedLinearSpace ℝ E] (c : ℝ) (x : E) :
    ‖c • x‖ = ‖c‖ * ‖x‖ := by
  exact norm_smul c x

/-- **范数收敛的 ε–N 判据**：序列拓扑收敛当且仅当其与极限之差的范数最终任意小。

这就是度量收敛判据在恒等式 `dist (u n) x = ‖u n-x‖` 下的直接转写。

> **Entry**: topology.normed-space.banach
@isnad1 id=iff.0h3v.s6.beadc795305c from=translated src=- shape=694a1fc8 vocab=24005ee0
-/
theorem tendsto_iff_norm_sub [_normedLinear : NormedLinearSpace ℝ E]
    {u : ℕ → E} {x : E} :
    Tendsto u atTop (nhds x) ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ‖u n - x‖ < ε := by
  simpa only [dist_eq_norm] using (Metric.tendsto_atTop (u := u) (a := x))

/-- **范数 Cauchy 判据**：任意足够靠后的两项之差的范数都任意小。
@isnad1 id=iff.0h2v.s6.ebc1ca2ae1f8 from=translated src=- shape=64276d1c vocab=c17029a4
-/
theorem cauchySeq_iff_norm_sub [_normedLinear : NormedLinearSpace ℝ E] {u : ℕ → E} :
    CauchySeq u ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖u m - u n‖ < ε := by
  simpa only [dist_eq_norm] using (Metric.cauchySeq_iff (u := u))

/-- **Banach 完备性**：Banach 空间中的每个 Cauchy 序列都收敛。
@isnad1 id=ex.1h2v.s5.d808150d0636 from=translated src=- shape=346cbdd2 vocab=af0f9ea0
-/
theorem cauchySeq_tendsto_of_banach [_normedLinear : NormedLinearSpace ℝ E]
    [BanachSpace E]
    {u : ℕ → E} (hu : CauchySeq u) : ∃ x : E, Tendsto u atTop (nhds x) := by
  exact cauchySeq_tendsto_of_complete hu

end SandronesLibrary.Topology.NormedSpace
