/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.CommutativeAlgebra.Module.Definition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# CommutativeAlgebra / Module —— 商模、自然投影与商映射的泛性质（Atiyah–Macdonald 第 2 章）

本文件承载条目 **commutative-algebra.module.quotient**（CA1 定义层）。

概念清单（教材概念 → Lean 正式承载）：

* **商模**：`M ⧸ p`。本版 Mathlib 里没有名为 `Submodule.Quotient` 的常量（`#check` 实测报
  `Unknown constant`），`Submodule.Quotient` 只是一个命名空间；商模就是「以陪集为元素、
  带 `Module R` 实例的商类型」，实例由 `Submodule.Quotient.module` 提供。本文件不另造包装结构。
* **自然投影**：两个层次——`Submodule.Quotient.mk : M → M ⧸ p`（函数，用于逐点陈述）与
  `Submodule.mkQ : M →ₗ[R] M ⧸ p`（线性映射，教材的 π，用于泛性质）。
* **陪集判等**：`Submodule.Quotient.eq`（`mk x = mk y ↔ x - y ∈ p`）与
  `Submodule.Quotient.mk_eq_zero`（`mk x = 0 ↔ x ∈ p`）。
* **商映射的泛性质**：存在性由 `Submodule.liftQ` 给出，唯一性由 `Submodule.linearMap_qext`
  推出；`quotient_liftQ_exists_unique` 是教材「存在唯一」的合取陈述。
* **商映射的函子性**：`Submodule.factor`（由 `p ≤ p'` 诱导 `M ⧸ p →ₗ[R] M ⧸ p'`）。

公开陈述一律写在 Atiyah–Macdonald 的设定 `[CommRing R] [AddCommGroup M]` 上；Mathlib 的承载
更一般（`Ring`/`AddCommGroup`），本文件不为迁就一般性而弱化教材陈述。
-/

namespace SandronesLibrary

namespace CommutativeAlgebra.Module

/-! ## 一、商模与自然投影 -/

/-- **陪集相等的判据**（Atiyah–Macdonald 第 2 章）：商模 `M ⧸ p` 中两个陪集 `x + p` 与 `y + p`
相等，当且仅当 `x - y ∈ p`。这是商模上元素相等的唯一判据，也是后面所有「良定义」证明的入口。
`M ⧸ p` 是商模的语义一致的正式承载，`Submodule.Quotient.eq` 给出该等价。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=iff.0h5v.s7.a5801a7856ba from=translated src=- shape=c70b1dc2 vocab=6cf01a7d
-/
theorem quotient_mk_eq_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) (x y : M) :
    (Submodule.Quotient.mk x : M ⧸ p) = Submodule.Quotient.mk y ↔ x - y ∈ p :=
  Submodule.Quotient.eq p

/-- **陪集等于零的判据**：商模中 `mk x = 0` 当且仅当 `x ∈ p`。这是上一条取 `y = 0` 的特例，
也是「自然投影的核是 `p`」的逐点版本；教材用它把「商模里的零」翻译回「`M` 里的 `p`」。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=iff.0h4v.s7.e2d9e37aa95d from=translated src=- shape=4c5a76c4 vocab=eb7c290a
-/
theorem quotient_mk_eq_zero_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) (x : M) :
    (Submodule.Quotient.mk x : M ⧸ p) = 0 ↔ x ∈ p :=
  Submodule.Quotient.mk_eq_zero p

/-- **商模的加法良定义**：`mk (x + y) = mk x + mk y`。教材把这条当作「商模是阿贝尔群」的验证
义务（换代表元不改变陪集的和）；在 Lean 里它是 `M ⧸ p` 的 `AddCommGroup` 实例的构造等式。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.0h5v.s8.3ad633bd338f from=translated src=- shape=760aec9b vocab=dc4def0c
-/
theorem quotient_mk_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) (x y : M) :
    (Submodule.Quotient.mk (x + y) : M ⧸ p) =
      Submodule.Quotient.mk x + Submodule.Quotient.mk y :=
  Submodule.Quotient.mk_add p

/-- **商模的数量乘良定义**：`mk (a • x) = a • mk x`。与加法同理，这是商模的 `Module R` 实例
（`Submodule.Quotient.module`）的构造等式，对应教材「数量乘与代表元选取无关」的验证。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.0h5v.s7.ebdc36a873ec from=translated src=- shape=f50249f9 vocab=8eb3d10c
-/
theorem quotient_mk_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) (a : R) (x : M) :
    (Submodule.Quotient.mk (a • x) : M ⧸ p) = a • Submodule.Quotient.mk x :=
  Submodule.Quotient.mk_smul p a x

/-- **自然投影的两个层次**：线性映射 `p.mkQ : M →ₗ[R] M ⧸ p` 与函数
`Submodule.Quotient.mk : M → M ⧸ p` 在元素上一致。教材只写一个 π；Lean 里必须区分「函数」
（用于陈述陪集相等）与「线性映射」（用于陈述泛性质），本定理把两者接起来。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.0h4v.s7.08efd9cbbef1 from=translated src=- shape=e767449a vocab=da1cd048
-/
theorem mkQ_apply_mk {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) (x : M) : p.mkQ x = Submodule.Quotient.mk x :=
  Submodule.mkQ_apply p x

/-- **自然投影的核恰是 `p`**：`ker π = p`。教材用「`π(x) = 0 ⟺ x ∈ p`」表达同一件事；
这是商模的第一个结构性质，也是同构定理 `M / ker f ≅ im f` 的起点（后者属下一批）。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.0h3v.s6.0b6840d3fd5e from=translated src=- shape=09e0c26f vocab=5e2f8792
-/
theorem mkQ_ker {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) : LinearMap.ker p.mkQ = p :=
  Submodule.ker_mkQ p

/-- **自然投影是满射**：`range π = ⊤`。教材的表述是「商模的每个元素都是某个 `x` 的陪集」，
即 π 满射；这也是商模泛性质中「唯一性只需在陪集上验证」的依据。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.0h3v.s8.bc814e30b643 from=translated src=- shape=62fcd8b6 vocab=a7534255
-/
theorem mkQ_range {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) : LinearMap.range p.mkQ = ⊤ :=
  Submodule.range_mkQ p

/-- **自然投影满射（函数形式）**：每个陪集都有代表元。`Submodule.mkQ_surjective` 给出；
本文件把它作为独立公开陈述，供上层在「取原像」时直接引用。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=surjecti.0h3v.s7.dca3b1d7498e from=translated src=- shape=7a089f75 vocab=28093c6f
-/
theorem mkQ_surjective {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) : Function.Surjective p.mkQ :=
  Submodule.mkQ_surjective p

/-! ## 二、商映射的泛性质 -/

/-- **商映射在陪集上的取值**：若 `p ≤ ker f`，则 `liftQ` 给出的商映射在 `mk x` 上取 `f x`。
这条等式是泛性质的「计算规则」，教材写作 `f̄(x + p) = f(x)`。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.1h6v.s8.cd5e739a1c53 from=translated src=- shape=7d90d13d vocab=cff0f4ca
-/
theorem quotient_liftQ_mk {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) (f : M →ₗ[R] N) (h : p ≤ LinearMap.ker f)
    (x : M) : p.liftQ f h (Submodule.Quotient.mk x) = f x :=
  Submodule.liftQ_apply p f x

/-- **商映射的交换性**：`liftQ f h ∘ π = f`。这是泛性质「图上交换」的精确形式，
也是唯一性陈述 `quotient_liftQ_unique` 的比较对象。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.1h5v.s8.a149064076bf from=translated src=- shape=45b8efa8 vocab=8d68ff36
-/
theorem quotient_liftQ_comp_mkQ {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) (f : M →ₗ[R] N) (h : p ≤ LinearMap.ker f) :
    (p.liftQ f h).comp p.mkQ = f :=
  Submodule.liftQ_mkQ p f h

/-- **商模的泛性质（存在唯一性）**（Atiyah–Macdonald 第 2 章命题 2.1 的模版本）：设 `f : M → N`
是模同态、`p` 是 `M` 的子模。则「存在唯一的模同态 `g : M ⧸ p → N` 使 `g ∘ π = f`」
当且仅当 `p ⊆ ker f`。

正向：设 `x ∈ p`，则 `π x = 0`，于是 `f x = g (π x) = g 0 = 0`。
反向：存在性取 `g = liftQ f h`（`Submodule.liftQ`），交换性由 `Submodule.liftQ_mkQ` 给出；
唯一性用商模同态外延 `Submodule.linearMap_qext`——两个同态与满射 π 复合后相等即相等。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=iff.0h5v.s8.b20e3746ce2a from=translated src=- shape=f4034e7c vocab=799772b4
-/
theorem quotient_liftQ_exists_unique {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (p : Submodule R M) (f : M →ₗ[R] N) :
    (∃! g : M ⧸ p →ₗ[R] N, g.comp p.mkQ = f) ↔ p ≤ LinearMap.ker f := by
  constructor
  · rintro ⟨g, hg, _⟩ x hx
    have h0 : p.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [LinearMap.mem_ker, ← LinearMap.congr_fun hg x]
    simp [h0]
  · intro h
    refine ⟨p.liftQ f h, Submodule.liftQ_mkQ p f h, ?_⟩
    intro g hg
    exact Submodule.linearMap_qext p (hg.trans (Submodule.liftQ_mkQ p f h).symm)

/-- **商映射的唯一性**：任何与 `f` 在 π 上复合相等的商映射都等于 `liftQ f h`。
这是泛性质中「唯一」那一半的独立陈述，教材通常写成「满足 `f̄ ∘ π = f` 的 `f̄` 至多一个」。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.2h6v.s8.79f693cfa18c from=translated src=- shape=b4c51000 vocab=8d68ff36
-/
theorem quotient_liftQ_unique {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) (f : M →ₗ[R] N) (h : p ≤ LinearMap.ker f)
    {g : M ⧸ p →ₗ[R] N} (hg : g.comp p.mkQ = f) : g = p.liftQ f h :=
  Submodule.linearMap_qext p (hg.trans (Submodule.liftQ_mkQ p f h).symm)

/-- **商模同态的外延性**：两个从 `M ⧸ p` 出发的模同态相等，当且仅当它们在每个陪集 `mk x`
上取值相同。因为 π 满射，验证只需在陪集上进行；这是商模上「先取代表元再计算」的合法性依据。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.1h6v.s9.e34d0079f904 from=translated src=- shape=56123ca4 vocab=3274dadf
-/
theorem quotient_hom_ext {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) {g₁ g₂ : M ⧸ p →ₗ[R] N}
    (h : ∀ x : M, g₁ (Submodule.Quotient.mk x) = g₂ (Submodule.Quotient.mk x)) : g₁ = g₂ :=
  Submodule.quot_hom_ext p g₁ g₂ h

/-! ## 三、商映射的函子性与极端情形 -/

/-- **商映射的函子性**：若 `p ≤ p'`，则存在模同态 `M ⧸ p →ₗ[R] M ⧸ p'`，把 `p` 的陪集送到
`p'` 的陪集。教材的写法是「商模对子模包含关系是函子性的」；它是第三同构定理
（本批下一 Entry）的构造原料。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=eq.1h5v.s9.45af3116245c from=translated src=- shape=8251dfdc vocab=0b960181
-/
theorem quotient_factor_mkQ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p p' : Submodule R M} (h : p ≤ p') (x : M) :
    Submodule.factor h (p.mkQ x) = p'.mkQ x :=
  Submodule.factor_mk h x

/-- **商映射的满射性**：`p ≤ p'` 诱导的商映射 `M ⧸ p → M ⧸ p'` 是满射。
教材的读法是「`M ⧸ p'` 是 `M ⧸ p` 的商」，这条是第三同构定理的满射那一半。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=surjecti.1h4v.s8.51e0363fb3e2 from=translated src=- shape=01e52730 vocab=83ec6eb0
-/
theorem quotient_factor_surjective {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p p' : Submodule R M} (h : p ≤ p') : Function.Surjective (Submodule.factor h) :=
  Submodule.factor_surjective h

/-- **商模平凡当且仅当商掉整个模**：`Subsingleton (M ⧸ p) ↔ p = ⊤`。教材的读法是
「`M / M = 0`，且只有商掉整个 `M` 才得到零模」，是商模的第一个极端情形。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=iff.0h3v.s6.cb0af538ec95 from=translated src=- shape=bef92f21 vocab=36f88d0b
-/
theorem quotient_subsingleton_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} : Subsingleton (M ⧸ p) ↔ p = ⊤ :=
  Submodule.Quotient.subsingleton_iff

/-- **商模非平凡当且仅当子模真包含**：`Nontrivial (M ⧸ p) ↔ p ≠ ⊤`。这是上一条的对偶写法，
也是「商模保留了多少信息」这一直觉的精确边界：只有 `p = ⊤` 时商模才塌缩成一点。
> **Entry**: commutative-algebra.module.quotient
@isnad1 id=iff.0h3v.s6.5eaba10febcd from=translated src=- shape=bef92f21 vocab=3d5b61ab
-/
theorem quotient_nontrivial_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} : Nontrivial (M ⧸ p) ↔ p ≠ ⊤ :=
  Submodule.Quotient.nontrivial_iff

/-- **商掉零子模得到自身**：`M ⧸ ⊥ ≃ₗ[R] M`。教材的第二个极端情形
（`M / 0 = M`），说明「商掉零子模」不损失任何信息。
> **Entry**: commutative-algebra.module.quotient-/
noncomputable def quotient_bot_equiv {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    (M ⧸ (⊥ : Submodule R M)) ≃ₗ[R] M :=
  Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl

end CommutativeAlgebra.Module

end SandronesLibrary
