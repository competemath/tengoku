/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.CommutativeAlgebra.Module.Definition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# CommutativeAlgebra / Module —— 内外直和与分解判据（Atiyah–Macdonald 第 2 章）

本文件承载条目 **commutative-algebra.module.direct-sum**（CA1）。

概念清单（教材概念 → Lean 正式承载）：

* **内直和（两项）**：子模 `p q` 互补，即「交为零」且「和是整个模」。Lean 正式承载是
  **序论谓词** `IsCompl p q`（`PartialOrder` + `BoundedOrder` 层面），不是 `Submodule` 专用
  谓词；`isCompl_iff_disjoint_sup_eq_top` 把它展开成 `Disjoint p q ∧ p ⊔ q = ⊤`，
  `Submodule.disjoint_def` 再把它落到逐元素命题。
* **分解判据**：`IsCompl p q ↔ ∀ x : M, ∃! yz : p × q, (yz.1 : M) + (yz.2 : M) = x`
  （`isCompl_iff_existsUnique_decomposition`），存在半与唯一性半分别由 `p ⊔ q = ⊤` 与
  `p ⊓ q = ⊥` 提供；两项情形的重组映射 `(y, z) ↦ y + z` 是
  `Submodule.prodEquivOfIsCompl`（`prodEquivOfIsCompl_apply`）。
* **外直和**：一族模 `M i` 的有限支撑族 `⨁ i, M i`。Lean 正式承载是 Mathlib 的
  `DirectSum ι M`（底层即 `DFinsupp`）；标准嵌入是 `DirectSum.lof`/`DirectSum.of`，
  坐标由 `DirectSum.of_eq_same`/`DirectSum.of_eq_of_ne` 与 `DirectSum.component` 读出；
  泛性质是 `DirectSum.toModule`（存在半，`directSum_toModule_lof`）加本文件自证的
  唯一性半（`directSum_toModule_unique`），打包成 `directSum_lof_ext_iff` 与
  `directSum_existsUnique_toModule`。
* **内 ↔ 外的桥**：Mathlib 用**族**版本的内直和 `DirectSum.Decomposition ℳ`
  （`ℳ : ι → Submodule R M`，带构造性逆）承载「`M` 分解成各 `ℳ i` 的直和」，
  桥是 `internalDirectSum_decomposeLinearEquiv ℳ : M ≃ₗ[R] ⨁ i, ℳ i`；
  两条分量刻画 `internalDirectSum_decompose_of_mem_same`/`_of_mem_ne` 说明该分解可计算。
* **两项情形下两个概念是同一件事**：`isCompl_iff_isInternal_fin_two` 给出
  `IsCompl p q ↔ DirectSum.IsInternal ![p, q]`，`decompositionOfIsCompl` 由互补性造出
  `DirectSum.Decomposition ![p, q]`，`isCompl_iff_nonempty_decomposition_fin_two` 把它补成
  **双向等价**「互补 ⟺ 分解结构存在」，`internalDirectSum_decomposeLinearEquiv_fin_two` 是它的
  同构形式。这是本条目把 (A) 与 (C) 焊在一起的桥，也是本文件里 `Classical.choice` 有实质
  使用的唯一来源（`chooseDecomposition`）。

公开陈述一律写在 Atiyah–Macdonald 的设定 `[CommRing R] [AddCommGroup M] [Module R M]` 上。
外直和块天然是「一族模」，因此那里把单个 `M` 换成族 `M : ι → Type*`（每个 `M i` 仍带
`[AddCommGroup]` 与 `[Module R]`）：这是教材 `⨁_{i ∈ I} M_i` 的忠实载体，不是把教材陈述
弱化到 Mathlib 的一般性（`Semiring`/`AddCommMonoid`）。
-/

open scoped DirectSum

namespace SandronesLibrary

namespace CommutativeAlgebra.Module

/-! ## (A) 内直和：两项互补与分解判据 -/

/-- **内直和的展开**（Atiyah–Macdonald 第 2 章）：两个子模 `p q` 互补（即 `M` 是内直和
`p ⊕ q`）当且仅当「`p` 与 `q` 的交只有零」且「`p + q` 是整个模 `M`」。`IsCompl` 是内直和的
正式承载，但它写在序论层面（`PartialOrder` + `BoundedOrder`），Mathlib 没有
`Submodule` 专用的 `IsCompl` 变体；本定理把它落到子模格的两个具体条件上。
证明只是 `isCompl_iff`（`IsCompl a b ↔ Disjoint a b ∧ Codisjoint a b`）与
`codisjoint_iff`（`Codisjoint a b ↔ a ⊔ b = ⊤`）两条展开的拼接。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem isCompl_iff_disjoint_sup_eq_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p q : Submodule R M) :
    IsCompl p q ↔ Disjoint p q ∧ p ⊔ q = ⊤ := by
  rw [isCompl_iff, codisjoint_iff]

/-- **和模的成员刻画**（Atiyah–Macdonald 第 2 章）：`x ∈ p + q` 当且仅当 `x` 能写成 `y + z`，
其中 `y ∈ p`、`z ∈ q`。这正是教材对子模之和的定义（「一切 `y + z` 的集合」），Lean 侧复用
`Submodule.mem_sup`。注意这里写的是 `p ⊔ q`——子模格的上确界就是教材的和。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem mem_sup_iff_exists_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} {x : M} :
    x ∈ p ⊔ q ↔ ∃ y ∈ p, ∃ z ∈ q, y + z = x :=
  Submodule.mem_sup

/-- **分解的存在半**：若 `p q` 互补，则每个 `x : M` 都能写成 `x = y + z`（`y ∈ p`、`z ∈ q`）。
证明走 `IsCompl.codisjoint`（即 `Codisjoint p q`）加 `codisjoint_iff` 得到 `p ⊔ q = ⊤`，
于是 `x ∈ p ⊔ q` 显然，再用 `mem_sup_iff_exists_add` 取出 `y`、`z`。这条对应教材
「`M = p + q` 蕴含每个元素可分解」。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem exists_add_of_isCompl {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : IsCompl p q) (x : M) :
    ∃ y ∈ p, ∃ z ∈ q, y + z = x :=
  Submodule.mem_sup.mp (by rw [codisjoint_iff.mp h.codisjoint]; exact Submodule.mem_top)

/-- **分解的唯一性半（分量形式）**：若 `p` 与 `q` 的交只有零，则对 `y y' ∈ p`、`z z' ∈ q`，
等式 `y + z = y' + z'` 成立**当且仅当** `y = y'` 且 `z = z'`。
证明是教材的标准移项：由 `y + z = y' + z'` 得 `y - y' = z' - z`，左端属于 `p`、右端属于 `q`，
故这个元素属于 `p ⊓ q = ⊥`，即 `y - y' = 0`（用 `Submodule.disjoint_def`），于是 `y = y'`；
再在等式中约去 `y'` 得 `z = z'`。反向是 `rfl`。这条是本文件分解判据的唯一性来源，
也说明「互补」比「和是整个模」多出来的那一半（`p ⊓ q = ⊥`）到底用在哪里。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem add_eq_add_iff_of_disjoint {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : Disjoint p q) {y y' : p} {z z' : q} :
    (y : M) + (z : M) = (y' : M) + (z' : M) ↔ y = y' ∧ z = z' := by
  constructor
  · intro hsum
    have heq : (y : M) - (y' : M) = (z' : M) - (z : M) := by
      rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
    have hyy' : (y : M) - (y' : M) ∈ p := p.sub_mem y.2 y'.2
    have hzz' : (y : M) - (y' : M) ∈ q := by rw [heq]; exact q.sub_mem z'.2 z.2
    have hzero : (y : M) - (y' : M) = 0 := Submodule.disjoint_def.mp h _ hyy' hzz'
    have h1 : y = y' := Subtype.ext (sub_eq_zero.mp hzero)
    have h1M : (y : M) = (y' : M) := Subtype.ext_iff.mp h1
    have h2 : (y' : M) + (z : M) = (y' : M) + (z' : M) := by
      have hh := hsum
      rw [h1M] at hh
      exact hh
    exact ⟨h1, Subtype.ext (add_left_cancel h2)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **分解的唯一性半（配对形式）**：`Disjoint p q` 时，同一个 `x` 的任意两个分解
`yz yz' : p × q`（即 `yz.1 + yz.2 = x` 且 `yz'.1 + yz'.2 = x`）相等。
这是上一条分量形式的直接改写，形态上可以直接喂给 `∃!`（`ExistsUnique.unique`）。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem decomposition_unique_of_disjoint {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : Disjoint p q) {x : M}
    {yz yz' : p × q} (h₁ : (yz.1 : M) + (yz.2 : M) = x)
    (h₂ : (yz'.1 : M) + (yz'.2 : M) = x) : yz = yz' := by
  have hsum : (yz.1 : M) + (yz.2 : M) = (yz'.1 : M) + (yz'.2 : M) := h₁.trans h₂.symm
  obtain ⟨h1, h2⟩ := (add_eq_add_iff_of_disjoint h).mp hsum
  exact Prod.ext h1 h2

/-- **分解判据**（Atiyah–Macdonald 第 2 章；本条目主定理）：子模 `p q` 互补当且仅当每个
`x : M` 都有**唯一**的分解 `x = y + z`（`y ∈ p`、`z ∈ q`），即
`∀ x : M, ∃! yz : p × q, (yz.1 : M) + (yz.2 : M) = x`。

* 正向：存在性来自 `p ⊔ q = ⊤`（`exists_add_of_isCompl`），唯一性来自 `Disjoint p q`
  （`decomposition_unique_of_disjoint`）。
* 反向：把唯一性用在 `x ∈ p ⊓ q` 上——`(x, 0)` 与 `(0, x)` 都是 `x` 的分解，故两个配对相等，
  比较第一分量得 `x = 0`，即 `p ⊓ q = ⊥`；再对每个 `x` 取其分解读出 `x ∈ p ⊔ q`，得
  `p ⊔ q = ⊤`。

两个方向都在本文件内自证，没有引用 Mathlib 的现成判据（`Submodule.isCompl_iff_disjoint` 只对
有限维除环上的子空间成立，不在教材设定 `[CommRing R]` 内）。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem isCompl_iff_existsUnique_decomposition {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (p q : Submodule R M) :
    IsCompl p q ↔ ∀ x : M, ∃! yz : p × q, (yz.1 : M) + (yz.2 : M) = x := by
  constructor
  · intro h x
    obtain ⟨y, hy, z, hz, hsum⟩ := exists_add_of_isCompl h x
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), hsum, fun yz' hyz' =>
      decomposition_unique_of_disjoint h.disjoint hyz' hsum⟩
  · intro h
    rw [isCompl_iff_disjoint_sup_eq_top]
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hy
      have hA : ((⟨x, hx⟩ : p) : M) + ((0 : q) : M) = x := by simp
      have hB : ((0 : p) : M) + ((⟨x, hy⟩ : q) : M) = x := by simp
      have hEq := (h x).unique (y₁ := ((⟨x, hx⟩ : p), (0 : q)))
        (y₂ := (((0 : p), (⟨x, hy⟩ : q)))) hA hB
      simpa using congrArg (fun t : p × q => (t.1 : M)) hEq
    · rw [Submodule.eq_top_iff']
      intro x
      obtain ⟨yz, hyz, -⟩ := h x
      exact Submodule.mem_sup.mpr ⟨yz.1, yz.1.2, yz.2, yz.2.2, hyz⟩

/-- **配对重组同构**：`Submodule.prodEquivOfIsCompl p q h : p × q ≃ₗ[R] M` 就是教材写的重组映射
`(y, z) ↦ y + z`。这是内直和「作为乘积」的载体层桥：分解判据说 `∃!` 的配对唯一，本定理说这个
配对与 `M` 之间的线性等价正是 `y + z`。Lean 侧复用 `Submodule.coe_prodEquivOfIsCompl'`
（Mathlib 已把它证成 `rfl`）；注意 `p q` 与 `h` 都是该定义的显式参数，`h` 在最后。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem prodEquivOfIsCompl_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p q : Submodule R M) (h : IsCompl p q) (yz : p × q) :
    Submodule.prodEquivOfIsCompl p q h yz = (yz.1 : M) + (yz.2 : M) :=
  Submodule.coe_prodEquivOfIsCompl' p q h yz

/-! ## (B) 外直和：坐标、标准嵌入与泛性质 -/

/-- **外直和的坐标（本位）**（Atiyah–Macdonald 第 2 章）：在 `⨁ i, M i` 中，第 `i` 个标准嵌入
`DirectSum.of M i x` 在第 `i` 个坐标处取值 `x`。教材说外直和的元素是**有限支撑族**，
「第 `i` 个坐标」就是族在 `i` 处的取值；Lean 的 `DirectSum` 底层就是 `DFinsupp`，
本定理是 `DirectSum.of_eq_same`。这里 `M : ι → Type*` 是一族 `R`-模——外直和的对象层级
本来就是族，不是单个模。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem directSum_of_apply_same {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (i : ι) (x : M i) :
    (DirectSum.of M i x) i = x :=
  DirectSum.of_eq_same i x

/-- **外直和的坐标（异位）**：`j ≠ i` 时 `DirectSum.of M i x` 的第 `j` 个坐标是 `0`。
与上一条合起来就是教材的「`of i` 把 `M i` 嵌进第 `i` 个坐标，其余坐标全为零」。
注意假设写成 `j ≠ i`（与 Mathlib 的 `DirectSum.of_eq_of_ne` 同序），不是 `i ≠ j`。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem directSum_of_apply_of_ne {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (i j : ι) (x : M i) (h : j ≠ i) : (DirectSum.of M i x) j = 0 :=
  DirectSum.of_eq_of_ne i j x h

/-- **外直和的泛性质：存在半**：给定一族线性映射 `φ i : M i →ₗ[R] N`，
`DirectSum.toModule R ι N φ` 是把它们「同时延拓」到整个外直和的线性映射，且在每个标准嵌入
`DirectSum.lof R ι M i`（`lof` 就是线性映射版本的标准嵌入，与加法版本的 `of` 是同一个映射）
上与 `φ i` 一致。本条只陈述这些等式（存在性）；唯一性见 `directSum_toModule_unique`。
Lean 侧复用 `DirectSum.toModule_lof`。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem directSum_toModule_lof {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ i, M i →ₗ[R] N) (i : ι) (x : M i) :
    DirectSum.toModule R ι N φ (DirectSum.lof R ι M i x) = φ i x :=
  DirectSum.toModule_lof R i x

/-- **外直和的泛性质：唯一性半**（本文件自证）：若线性映射 `g : (⨁ i, M i) →ₗ[R] N` 在每个
标准嵌入上与 `φ` 一致，则 `g` 就是 `DirectSum.toModule R ι N φ`。

Mathlib 里没有**整体形式**的这条定理（`DirectSum.toModule_unique` 不存在；它有的是逐元素形式
`DirectSum.toModule.unique` 与 `@[ext]` 形式 `DirectSum.linearMap_ext`），所以这里按教材
重新证明：外直和的每个元素由 `0`、单项 `of i x` 与加法生成（`DirectSum.induction_on`），
三支分别用 `simp`、`DirectSum.lof_eq_of` + `toModule_lof`、`map_add` + 归纳假设。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem directSum_toModule_unique {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ i, M i →ₗ[R] N)
    (g : (⨁ i, M i) →ₗ[R] N) (hg : ∀ (i : ι) (x : M i), g (DirectSum.lof R ι M i x) = φ i x) :
    g = DirectSum.toModule R ι N φ := by
  apply LinearMap.ext
  intro v
  refine DirectSum.induction_on v ?_ ?_ ?_
  · simp
  · intro i x
    rw [← DirectSum.lof_eq_of R ι M i x, hg i x, DirectSum.toModule_lof]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]

/-- **泛性质的 iff 打包**：线性映射 `g : (⨁ i, M i) →ₗ[R] N` 等于 `DirectSum.toModule R ι N φ`
**当且仅当**它在每个标准嵌入 `lof i` 上与 `φ i` 一致。正向是把 `toModule_lof` 代进等式，
反向是上一条唯一性。这条 iff 是教材「外直和由各分量上的取值唯一决定」的精确表述。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem directSum_lof_ext_iff {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ i, M i →ₗ[R] N) (g : (⨁ i, M i) →ₗ[R] N) :
    g = DirectSum.toModule R ι N φ ↔ ∀ (i : ι) (x : M i), g (DirectSum.lof R ι M i x) = φ i x :=
  ⟨fun h i x => by rw [h, DirectSum.toModule_lof], fun hg => directSum_toModule_unique φ g hg⟩

/-- **外直和的泛性质（存在唯一）**：对任意一族线性映射 `φ`，满足
`∀ i x, g (lof i x) = φ i x` 的线性映射 `g : (⨁ i, M i) →ₗ[R] N` **存在且唯一**。
这是把存在半（`directSum_toModule_lof`）与唯一性半（`directSum_toModule_unique`）合成一条
教材陈述的结果，也是外直和「是所有 `M i` 的余积」这句话在模层面的全部内容。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem directSum_existsUnique_toModule {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ i, M i →ₗ[R] N) :
    ∃! g : (⨁ i, M i) →ₗ[R] N, ∀ (i : ι) (x : M i), g (DirectSum.lof R ι M i x) = φ i x :=
  ⟨DirectSum.toModule R ι N φ, fun i x => DirectSum.toModule_lof R i x,
    fun g hg => (directSum_lof_ext_iff φ g).mpr hg⟩

/-- **坐标映射就是取值**：`DirectSum.component R ι M i` 作用在 `v : ⨁ i, M i` 上等于 `v i`。
Mathlib 里 `DirectSum.component` 是第 `i` 个坐标投影（`DFinsupp.lapply` 的线性映射版本），
本定理（证明是 `rfl`）说明它与「把 `v` 当成有限支撑族求值」是同一个东西——这正是教材
「外直和的元素 = 有限支撑族」的 Lean 表述，也是后面把分解写成坐标的语言。
注意本条**不需要** `[DecidableEq ι]`：坐标投影与求值都是无判等的（编译器实测），
所以不写多余的假设。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem directSum_component_apply {R : Type*} [CommRing R] {ι : Type*}
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (i : ι) (v : ⨁ i, M i) : DirectSum.component R ι M i v = v i :=
  rfl

/-! ## (C) 内 ↔ 外的桥：`DirectSum.Decomposition` 与两项情形的焊合 -/

/-- **内直和的族版本（桥）**：在 `[DirectSum.Decomposition ℳ]` 下，`M` 线性同构于外直和
`⨁ i, ℳ i`。`DirectSum.Decomposition ℳ` 是 Mathlib 对「`M` 是各子模 `ℳ i` 的内直和」的
正式承载：它不是一条命题，而是一个**带数据的类**（一个映射 `M → ⨁ i, ℳ i` 加上它是
「重组映射」的左右逆的证明），因此比「`⨆ i, ℳ i = ⊤` 且各分量线性无关」更强、更可计算。
本定义是 (A) 的两项 `IsCompl` 与 (C) 的族版本之间的公开桥：
`internalDirectSum_decomposeLinearEquiv ℳ : M ≃ₗ[R] ⨁ i, ℳ i`。
> **Entry**: commutative-algebra.module.direct-sum-/
noncomputable def internalDirectSum_decomposeLinearEquiv {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module R M] (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ] : M ≃ₗ[R] ⨁ i, ℳ i :=
  DirectSum.decomposeLinearEquiv ℳ

/-- **分量刻画（本位）**：若 `x ∈ ℳ i`，则 `x` 在分解同构下的第 `i` 个分量就是 `x` 本身
（子类型意义下）。这条与下一条一起说明「分解」是可计算的：落在某个分量里的元素，其坐标是
已知的。Lean 侧复用 `DirectSum.decompose_of_mem_same`。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem internalDirectSum_decompose_of_mem_same {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module R M] (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ] {x : M} {i : ι} (hx : x ∈ ℳ i) :
    ((internalDirectSum_decomposeLinearEquiv ℳ x) i : M) = x :=
  DirectSum.decompose_of_mem_same ℳ hx

/-- **分量刻画（异位）**：若 `x ∈ ℳ i` 且 `j ≠ i`，则 `x` 的第 `j` 个分量是 `0`。
与上一条合起来就是教材的「分解到各分量上，只有所属的那一个分量非零」。
Lean 侧复用 `DirectSum.decompose_of_mem_ne`。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem internalDirectSum_decompose_of_mem_ne {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module R M] (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ] {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    ((internalDirectSum_decomposeLinearEquiv ℳ x) j : M) = 0 :=
  DirectSum.decompose_of_mem_ne ℳ hx hij

/-- **桥的逆就是重组**：把第 `i` 个分量里的元素 `x` 用标准嵌入 `lof i` 送进外直和，再用桥的
逆送回来，得到 `x`。这是 (C) 里与 (A) 的 `prodEquivOfIsCompl_apply` 对应的那一半：
(A) 说配对重组是 `(y, z) ↦ y + z`，(C) 说族版本的重组是逐分量的标准嵌入。
Lean 侧复用 `DirectSum.decomposeLinearEquiv_symm_lof`。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem internalDirectSum_decomposeLinearEquiv_symm_lof {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module R M] (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ] (i : ι) (x : ℳ i) :
    (internalDirectSum_decomposeLinearEquiv ℳ).symm (DirectSum.lof R ι (fun i => ℳ i) i x) = x :=
  DirectSum.decomposeLinearEquiv_symm_lof ℳ i x

/-- **两项情形：`IsCompl` 就是 `DirectSum.IsInternal`**：当指标集只有两个元素 `0, 1` 时，
子模族 `![p, q]` 是内直和（`DirectSum.IsInternal`）当且仅当 `p` 与 `q` 互补。
这是本条目最重要的一条**桥**：它说明 (A) 的两项 `IsCompl` 与 (C) 的族版本内直和不是两套
数学，而是同一个概念的两种拼写。Lean 侧复用
`DirectSum.isInternal_submodule_iff_isCompl`（它要求指标集恰为 `{i, j}`，这里 `i, j = 0, 1`）。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem isCompl_iff_isInternal_fin_two {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (p q : Submodule R M) :
    IsCompl p q ↔ DirectSum.IsInternal ![p, q] := by
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i
    fin_cases i <;> simp
  rw [DirectSum.isInternal_submodule_iff_isCompl ![p, q] (by decide) huniv]
  simp

/-- **由互补性造出分解结构**：`IsCompl p q` 给出 `DirectSum.Decomposition ![p, q]`，
即 `M` 是 `p` 与 `q` 的内直和（族版本，带构造性逆）。这是把 (A) 的概念真正搬进 (C) 的
语言的一步：先经 `isCompl_iff_isInternal_fin_two` 得到 `DirectSum.IsInternal ![p, q]`，
再用 Mathlib 的 `DirectSum.IsInternal.chooseDecomposition` 取出分解结构。

诚实边界：这条证明走 `chooseDecomposition`，它用 `Equiv.ofBijective` 从双射**非计算地**
取出逆映射，因此本定义带 `Classical.choice`；本文件没有手写 `Submodule.projectionOnto`
版本的分解映射。另外它是 `def` 而不是全局 `instance`——`IsCompl p q` 不是类型类，
写成 `instance` 只会污染实例搜索而几乎搜不到；需要时用 `letI` 局部装载（见
`internalDirectSum_decomposeLinearEquiv_fin_two`）。
> **Entry**: commutative-algebra.module.direct-sum-/
@[instance_reducible]
noncomputable def decompositionOfIsCompl {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (p q : Submodule R M) (h : IsCompl p q) :
    DirectSum.Decomposition ![p, q] :=
  DirectSum.IsInternal.chooseDecomposition _ ((isCompl_iff_isInternal_fin_two p q).mp h)

/-- **两项情形的落地（(A) 与 (C) 焊合）**：若 `p q` 互补，则 `M` 线性同构于外直和
`⨁ i : Fin 2, ![p, q] i`。这是把 (A) 的 `IsCompl` 与 (C) 的分解同构接起来的收口定理：
`decompositionOfIsCompl` 先把互补性变成 `DirectSum.Decomposition ![p, q]`，
再把 `internalDirectSum_decomposeLinearEquiv` 应用上去。
> **Entry**: commutative-algebra.module.direct-sum-/
noncomputable def internalDirectSum_decomposeLinearEquiv_fin_two {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (p q : Submodule R M) (h : IsCompl p q) :
    M ≃ₗ[R] ⨁ i : Fin 2, ![p, q] i := by
  letI := decompositionOfIsCompl p q h
  exact internalDirectSum_decomposeLinearEquiv ![p, q]

/-- **两项情形：互补 ⟺ 存在分解结构**：`p q` 互补当且仅当存在 `DirectSum.Decomposition ![p, q]`。
上一条给的是 `IsCompl ↔ DirectSum.IsInternal`（命题版内直和），本条把它推进到带数据的
`Decomposition`（构造版内直和）：正向由 `decompositionOfIsCompl` 提供分解结构，反向由
`DirectSum.Decomposition.isInternal`（Mathlib）取出命题版内直和，再翻译回互补性。
由于 Mathlib 已证 `DirectSum.Decomposition` 有 `Subsingleton` 实例，`Nonempty` 是「分解结构
存在」这个命题的诚实写法——不会把带数据的类硬塞进 `↔` 的一侧。
至此 (A) 的两项 `IsCompl` 与 (C) 的族版本分解在本文件里是**双向等价**的两种拼写。
> **Entry**: commutative-algebra.module.direct-sum-/
theorem isCompl_iff_nonempty_decomposition_fin_two {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (p q : Submodule R M) :
    IsCompl p q ↔ Nonempty (DirectSum.Decomposition ![p, q]) :=
  ⟨fun h => ⟨decompositionOfIsCompl p q h⟩,
    fun ⟨d⟩ => (isCompl_iff_isInternal_fin_two p q).mpr d.isInternal⟩

end CommutativeAlgebra.Module

end SandronesLibrary
