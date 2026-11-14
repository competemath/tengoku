/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.CommutativeAlgebra.Module.Definition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# CommutativeAlgebra / Module —— 子集生成的子模与最小性（Atiyah–Macdonald 第 2 章）

本文件承载条目 **commutative-algebra.module.generated**（CA1 生成层）。

概念清单（教材概念 → Lean 正式承载）：

* **由子集生成的子模** `⟨s⟩`：含 `s` 的最小子模。Lean 正式承载是 Mathlib 的
  `Submodule.span R s`；本文件不另造平行结构（AGENTS §4：不为制造本库名称重造等价结构），
  也不为它新设记号。
* **最小性**：教材「`⟨s⟩` 是含 `s` 的最小子模」这一句话在 Lean 里有三张等价的脸——
  元素层（`mem_span_iff`：`x ∈ ⟨s⟩` 当且仅当 `x` 属于每个含 `s` 的子模）、
  序层伴随形式（`span_le_iff_subset`：`⟨s⟩ ≤ p` 当且仅当 `s ⊆ p`）、
  最小子模形式（`span_eq_iff_subset_and_le`：`⟨s⟩ = p` 当且仅当 `p` 含 `s` 且含于每个含 `s`
  的子模），外加交形式（`span_eq_sInf`：`⟨s⟩` 是全体含 `s` 的子模之交）。
* **归纳原理**：`span_induction`——性质若在 `s` 上成立且对 `0`、`+`、`•` 封闭，
  则在 `⟨s⟩` 上处处成立；这就是「`⟨s⟩` 的元素由 `s` 经 `0`、`+`、`•` 生成」的严格说法。
* **span 的基本演算**：包含（`subset_span`）、对生成集单调（`span_mono`）、
  两条幂等（`span_eq_of_submodule`、`span_span`）、空集与全集（`span_empty`、`span_univ`）、
  并集（`span_union`）、零子模判定（`span_eq_bot_iff`）、单元素生成（`mem_span_singleton_iff`）。
* **上层使用者**：`map_span`——模同态把 `⟨s⟩` 映到 `⟨F '' s⟩`，这是 `Submodule.span`
  作为正式承载在本条目内被真实使用的地方。

公开陈述一律写在 Atiyah–Macdonald 的设定 `[CommRing R] [AddCommGroup M] [Module R M]` 上；
Mathlib 的承载更一般（`Semiring`/`AddCommMonoid`），本文件不为迁就一般性而弱化教材陈述。
-/

namespace SandronesLibrary

namespace CommutativeAlgebra.Module

/-- **生成子模包含原集合**（Atiyah–Macdonald 第 2 章）：`s ⊆ ⟨s⟩`。
`Submodule.span R s` 是教材 `⟨s⟩` 的语义一致的正式承载；这条是「含 `s`」那一半，
与下面的最小性合起来才是「含 `s` 的最小子模」。
> **Entry**: commutative-algebra.module.generated-/
theorem subset_span {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {s : Set M} : s ⊆ Submodule.span R s :=
  Submodule.subset_span

/-- **最小性（元素层）**（Atiyah–Macdonald 第 2 章）：`x ∈ ⟨s⟩` 当且仅当 `x` 属于每个
包含 `s` 的子模。这是「最小」在元素上的展开：属于 `⟨s⟩` 就是被所有含 `s` 的子模共享。
> **Entry**: commutative-algebra.module.generated-/
theorem mem_span_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : Set M) (x : M) :
    x ∈ Submodule.span R s ↔ ∀ p : Submodule R M, s ⊆ p → x ∈ p :=
  Submodule.mem_span

/-- **最小性（序层，伴随形式）**（Atiyah–Macdonald 第 2 章）：`⟨s⟩ ≤ p` 当且仅当 `s ⊆ p`。
这是「最小」作为子模格中最小上界的标准形式：`span R` 是含入函子 `s ↦ s` 的左伴随，
`⟨s⟩` 是 `s` 在子模格里的下界中最小的那个。
> **Entry**: commutative-algebra.module.generated-/
theorem span_le_iff_subset {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : Set M) (p : Submodule R M) :
    Submodule.span R s ≤ p ↔ s ⊆ p :=
  Submodule.span_le

/-- **最小性（最小子模形式）**（Atiyah–Macdonald 第 2 章）：`⟨s⟩ = p` 当且仅当
`p` 包含 `s`，且 `p` 含于每个包含 `s` 的子模。这是教材原话「`⟨s⟩` 是包含 `s` 的最小子模」
的直接形式化：右式的第一条说 `p` 有资格当候选，第二条说它是最小的那个。
正向由 `subset_span` 与 `span_le_iff_subset` 给出，反向由子模格的反对称性给出。
> **Entry**: commutative-algebra.module.generated-/
theorem span_eq_iff_subset_and_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : Set M) (p : Submodule R M) :
    Submodule.span R s = p ↔ s ⊆ p ∧ ∀ q : Submodule R M, s ⊆ q → p ≤ q := by
  constructor
  · intro h
    subst h
    exact ⟨subset_span, fun q hq => (span_le_iff_subset s q).mpr hq⟩
  · rintro ⟨hsp, hleast⟩
    exact le_antisymm ((span_le_iff_subset s p).mpr hsp) (hleast _ subset_span)

/-- **最小性（交形式）**（Atiyah–Macdonald 第 2 章）：`⟨s⟩` 等于全体包含 `s` 的子模之交。
子模格是完备格，「最小」既可以写成上一条的「含于每个候选」，也可以写成这里的「等于候选之交」；
两种写法在本条目里互为对照。本版 Mathlib 直接把 `Submodule.span R s` 定义为
`sInf {p | s ⊆ p}`，所以这条在本版是定义展开（`rfl`），不是需要另找证明的数学内容；
证明体写成 `rfl` 也顺带避免了走 `le_sInf`/`sInf_le` 把 `Classical.choice` 带进公理档案。
> **Entry**: commutative-algebra.module.generated-/
theorem span_eq_sInf {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : Set M) :
    Submodule.span R s = sInf {p : Submodule R M | s ⊆ p} :=
  rfl

/-- **归纳原理**（Atiyah–Macdonald 第 2 章）：若性质 `P` 在 `s` 上成立，且对 `0` 封闭、
对加法封闭、对数乘封闭，则 `P` 在 `⟨s⟩` 上处处成立。这是「`⟨s⟩` 的元素由 `s` 经
`0`、`+`、`•` 生成」的严格说法：任何包含 `s` 且对三条运算封闭的性质都自动在整个 `⟨s⟩` 上成立。
Mathlib 的 `Submodule.span_induction` 用的是带证明项的 motive
`p : (x : M) → x ∈ span R s → Prop`，本条把它包装成教材的 `P : M → Prop` 形式。
> **Entry**: commutative-algebra.module.generated-/
theorem span_induction {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {s : Set M} {P : M → Prop}
    (mem : ∀ x ∈ s, P x) (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (a : R) x, P x → P (a • x)) :
    ∀ x ∈ Submodule.span R s, P x := by
  intro x hx
  exact Submodule.span_induction (fun x hx => mem x hx) zero
    (fun x y _ _ hx hy => add x y hx hy) (fun a x _ hx => smul a x hx) hx

/-- **生成子模对生成集单调**（Atiyah–Macdonald 第 2 章）：`s ⊆ t` 蕴含 `⟨s⟩ ≤ ⟨t⟩`。
由最小性的序层形式直接得到：`⟨s⟩ ≤ ⟨t⟩` 等价于 `s ⊆ ⟨t⟩`，而后者由 `s ⊆ t ⊆ ⟨t⟩` 给出。
证明体正是这个推导（复用本文件的 `span_le_iff_subset` 与 `subset_span`，不走 Mathlib
`Submodule.span_mono`）；合成 `s ⊆ t ⊆ ⟨t⟩` 时用显式 `Set.Subset.trans` 而不是点记号 `h.trans`，
后者会经 `Trans` 实例把 `Classical.choice` 带进公理档案（见本条目文档「应用与陷阱」）。
> **Entry**: commutative-algebra.module.generated-/
theorem span_mono {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {s t : Set M} (h : s ⊆ t) : Submodule.span R s ≤ Submodule.span R t :=
  (span_le_iff_subset s (Submodule.span R t)).mpr (Set.Subset.trans h subset_span)

/-- **子模的生成幂等**（Atiyah–Macdonald 第 2 章）：若生成集本身是子模 `p` 的载体，
则 `⟨p⟩ = p`。这正是「子模已经对 `0`、`+`、`•` 封闭，无需再生成」。
> **Entry**: commutative-algebra.module.generated-/
theorem span_eq_of_submodule {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) : Submodule.span R (p : Set M) = p :=
  Submodule.span_eq p

/-- **生成子的生成幂等**（Atiyah–Macdonald 第 2 章）：`⟨⟨s⟩⟩ = ⟨s⟩`。
由 `span_eq_of_submodule` 作用在子模 `⟨s⟩` 上得到，说明「生成」这一操作是幂等的
（闭包算子的三条性质在本条目里分别是 `subset_span`、`span_mono`、本条）。
> **Entry**: commutative-algebra.module.generated-/
theorem span_span {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : Set M) :
    Submodule.span R (Submodule.span R s : Set M) = Submodule.span R s :=
  span_eq_of_submodule (Submodule.span R s)

/-- **空集生成零子模**（Atiyah–Macdonald 第 2 章）：`⟨∅⟩ = ⊥`。
空集没有元素可生成，最小的候选只剩零子模；证明用最小性（`⟨∅⟩ ≤ ⊥`，因为 `∅ ⊆ ⊥`）
与 `⊥` 的最小性两条夹出，不走 Mathlib `Submodule.span_empty` 的 `GaloisInsertion` 证明路径
（那条路径会把 `Classical.choice` 带进公理档案，见本条目文档的「Mathlib 角色分类」一节）。
> **Entry**: commutative-algebra.module.generated-/
theorem span_empty {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Submodule.span R (∅ : Set M) = ⊥ :=
  le_antisymm (Submodule.span_le.2 (Set.empty_subset _)) bot_le

/-- **全集生成整个模**（Atiyah–Macdonald 第 2 章）：`⟨univ⟩ = ⊤`。
整个模本身就含 `univ` 且是子模，由最小性即得；证明用 `eq_top_iff'`（每个 `x` 都在 `univ` 里，
再由 `subset_span` 属于 `⟨univ⟩`）配合 `⊤` 的最大性，复用本文件的 `subset_span`。
> **Entry**: commutative-algebra.module.generated-/
theorem span_univ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Submodule.span R (Set.univ : Set M) = ⊤ :=
  Submodule.eq_top_iff'.mpr fun x => subset_span (Set.mem_univ x)

/-- **并集的生成等于生成子模的上确界**（Atiyah–Macdonald 第 2 章）：
`⟨s ∪ t⟩ = ⟨s⟩ ⊔ ⟨t⟩`。两边互相包含：右边由最小性（`⟨s⟩ ≤ ⟨s ∪ t⟩`、`⟨t⟩ ≤ ⟨s ∪ t⟩`）
给出，左边由 `s ∪ t ⊆ ⟨s⟩ ⊔ ⟨t⟩` 经最小性给出。证明按教材这个「两个包含」直接写出。
诚实披露：本条的类型含子模格的 `⊔`，而本版 Mathlib 的 `Sup (Submodule R M)` 实例定义体
是经典的，所以 `#print axioms` 会报 `Classical.choice`；这是类型级噪声（Playbook §3.3），
不是本条的数学内容需要选择公理。
> **Entry**: commutative-algebra.module.generated-/
theorem span_union {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s t : Set M) :
    Submodule.span R (s ∪ t) = Submodule.span R s ⊔ Submodule.span R t := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x (hx | hx)
    · exact (le_sup_left : Submodule.span R s ≤ Submodule.span R s ⊔ Submodule.span R t)
        (Submodule.subset_span hx)
    · exact (le_sup_right : Submodule.span R t ≤ Submodule.span R s ⊔ Submodule.span R t)
        (Submodule.subset_span hx)
  · refine sup_le ?_ ?_
    · exact Submodule.span_le.2 (Set.Subset.trans Set.subset_union_left Submodule.subset_span)
    · exact Submodule.span_le.2 (Set.Subset.trans Set.subset_union_right Submodule.subset_span)

/-- **零子模判定**（Atiyah–Macdonald 第 2 章）：`⟨s⟩ = ⊥` 当且仅当 `s` 的每个元素都是 `0`。
左到右是「`s ⊆ ⟨s⟩ = ⊥`」，右到左是「零子模含 `s`，由最小性 `⟨s⟩ ≤ ⊥`」；
证明体按这两句话写出（复用本文件的 `subset_span` 与 `span_le_iff_subset`）。
> **Entry**: commutative-algebra.module.generated-/
theorem span_eq_bot_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {s : Set M} : Submodule.span R s = ⊥ ↔ ∀ x ∈ s, x = 0 :=
  ⟨fun h x hx => by
      have hx' : x ∈ Submodule.span R s := subset_span hx
      rw [h] at hx'
      exact hx',
    fun h => le_antisymm
      ((span_le_iff_subset s ⊥).mpr fun x hx => (Submodule.mem_bot R).mpr (h x hx)) bot_le⟩

/-- **单元素生成的子模**（Atiyah–Macdonald 第 2 章）：`x ∈ R ∙ y` 当且仅当 `x` 是 `y` 的
纯量倍，即存在 `a : R` 使 `a • y = x`。`R ∙ y` 是 Mathlib 对 `Submodule.span R {y}` 的记号，
本条是教材「由一个元素生成的子模」的成员刻画。
> **Entry**: commutative-algebra.module.generated-/
theorem mem_span_singleton_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x y : M) : x ∈ R ∙ y ↔ ∃ a : R, a • y = x :=
  Submodule.mem_span_singleton

/-- **生成子模的像由像集生成**（上层使用者）：对模同态 `F : M →ₗ[R] N`，
`F(⟨s⟩) = ⟨F '' s⟩`，即 `Submodule.map F (Submodule.span R s) = Submodule.span R (F '' s)`。
这是 `Submodule.span` 在本条目内被真实使用的公开定理：它把「生成」与「模同态的像」交换。
公开陈述冻结在线性形式 `M →ₗ[R] N`：Mathlib 的 `Submodule.map_span` 是半线性的、带显式
`[RingHomSurjective σ₁₂]` 假设，而在线性形式下 `RingHomSurjective (RingHom.id R)` 由类型类
合成自动提供，不会作为假设出现在本条的公开签名里。证明按教材的两个包含直接写出
（`map F ⟨s⟩ ≤ ⟨F '' s⟩` 用 `map_le_iff_le_comap` 与最小性；反向用最小性与 `mem_map_of_mem`），
既不需要 `RingHomSurjective`，也不走 Mathlib `map_span` 的证明路径。
> **Entry**: commutative-algebra.module.generated-/
theorem map_span {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (F : M →ₗ[R] N) (s : Set M) :
    Submodule.map F (Submodule.span R s) = Submodule.span R (F '' s) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · rw [Submodule.span_le]
    rintro y ⟨x, hx, rfl⟩
    exact Submodule.mem_map_of_mem (Submodule.subset_span hx)

end CommutativeAlgebra.Module

end SandronesLibrary
