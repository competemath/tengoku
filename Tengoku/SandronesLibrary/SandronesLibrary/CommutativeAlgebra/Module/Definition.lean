/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.Subspace
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# CommutativeAlgebra / Module —— 模、子模与模同态（Atiyah–Macdonald 第 2 章）

本文件承载条目 **commutative-algebra.module.definition**（CA1 定义层）。

概念清单（教材概念 → Lean 正式承载）：

* **模**：环 `R` 上的加法交换群 `M`，带满足教材六条公理的数量乘法。Lean 正式承载是
  Mathlib 的 `Module R M` 类：其父类 `DistribMulAction` 已含 `smul_add`、`mul_smul`、
  `one_smul`、`smul_zero` 四条，`Module` 自有字段只有 `add_smul` 与 `zero_smul`；
  `module_axioms` 把六条公理逐条展开成可审阅的合取式。
* **子模**：含零元、对加法与数乘封闭的子集。Lean 正式承载是 `Submodule R M`；
  `submodule_closure` 是三条封闭性的展开，`submodule_of_closure` 是反向构造，
  `submodule_eq_iff` 是外延性。
* **模同态**：保持加法与数乘的映射。Lean 正式承载是 `LinearMap R M N`（本版 Mathlib 的
  父结构是 `AddHom`，不是 `AddMonoidHom`）；`linearMap_iff` 把「是模同态」展开为两条保持性，
  `linearMap_ext_iff` 是外延性，`linearMap_map_zero` 是零元保持。
* **核与像**：`LinearMap.ker`、`LinearMap.range` 都是 `Submodule`，是子模承载的真实上层使用者。
* **本库桥**：`isSubspace_iff_exists_submodule`（L1 教材谓词 `IsSubspace` ↔ `Submodule`）、
  `twoSidedIdealSet_iff_exists_submodule_self`（A2 教材谓词 `TwoSidedIdealSet` ↔ `Submodule R R`）。

公开陈述一律写在 Atiyah–Macdonald 的设定 `[CommRing R]` 上；Mathlib 的承载更一般
（`Semiring`/`AddCommMonoid`），本文件不为迁就一般性而弱化教材陈述。
-/

namespace SandronesLibrary

namespace CommutativeAlgebra.Module

open SandronesLibrary.LinearAlgebra.VectorSpace

/-- **模的六条公理**（Atiyah–Macdonald 第 2 章）：环 `R` 上模 `M` 的数量乘法满足两条分配律、
结合律、单位律与两条零律。`Module R M` 是语义一致的正式承载：前四条与 `r • 0 = 0` 来自其父类
`DistribMulAction`/`SMulZeroClass`，`Module` 自有字段只有 `(r + s) • x = r • x + s • x` 与
`(0 : R) • x = 0`。
> **Entry**: commutative-algebra.module.definition-/
theorem module_axioms {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (r s : R) (x y : M) :
    r • (x + y) = r • x + r • y ∧ (r + s) • x = r • x + s • x ∧
      (r * s) • x = r • (s • x) ∧ (1 : R) • x = x ∧ (0 : R) • x = 0 ∧ r • (0 : M) = 0 :=
  ⟨smul_add r x y, add_smul r s x, mul_smul r s x, one_smul R x, zero_smul R x, smul_zero r⟩

/-- **子模的三条封闭性**（Atiyah–Macdonald 第 2 章）：子模含零元、对加法封闭、对数乘封闭。
`Submodule R M` 是子模的语义一致的正式承载（Mathlib 以 `carrier` 加三条封闭性字段打包）。
> **Entry**: commutative-algebra.module.definition-/
theorem submodule_closure {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) :
    (0 : M) ∈ S ∧ (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) ∧ (∀ (a : R) (x : M), x ∈ S → a • x ∈ S) :=
  ⟨S.zero_mem, fun _x hx _y hy => S.add_mem hx hy, fun a _x hx => S.smul_mem a hx⟩

/-- **由封闭性构造子模**：给定子集 `s` 含零元、对加法封闭、对数乘封闭，则存在以 `s` 为载体的
子模。这是 `Submodule R M` 作为正式承载的反向构造（教材「子模的等价定义」一侧）。
> **Entry**: commutative-algebra.module.definition-/
theorem submodule_of_closure {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {s : Set M} (h0 : (0 : M) ∈ s) (hadd : ∀ x ∈ s, ∀ y ∈ s, x + y ∈ s)
    (hsmul : ∀ (a : R) (x : M), x ∈ s → a • x ∈ s) :
    ∃ S : Submodule R M, (S : Set M) = s :=
  ⟨{ carrier := s, zero_mem' := h0, add_mem' := fun {x y} hx hy => hadd x hx y hy,
     smul_mem' := fun a {x} hx => hsmul a x hx }, rfl⟩

/-- **子模的外延性**：两个子模相等当且仅当它们有相同的元素。`Submodule R M` 是语义一致的
正式承载，`SetLike.ext_iff` 给出该外延性原理。
> **Entry**: commutative-algebra.module.definition-/
theorem submodule_eq_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {S T : Submodule R M} : S = T ↔ ∀ x, x ∈ S ↔ x ∈ T :=
  SetLike.ext_iff

/-- **模同态的展开**（Atiyah–Macdonald 第 2 章）：映射 `f : M → N` 是模同态，当且仅当它保持加法
与数乘。`LinearMap R M N` 是模同态的语义一致的正式承载（本版 Mathlib 的父结构是 `AddHom`，
`AddMonoidHom.toLinearMap` 不存在）；正向由 `F.map_add`/`F.map_smul` 给出，反向用
`LinearMap.mk (AddHom.mk f …) …` 组装。
> **Entry**: commutative-algebra.module.definition-/
theorem linearMap_iff {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M → N) :
    (∃ F : M →ₗ[R] N, ⇑F = f) ↔
      (∀ x y : M, f (x + y) = f x + f y) ∧ (∀ (a : R) (x : M), f (a • x) = a • f x) := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.map_add, F.map_smul⟩
  · rintro ⟨hadd, hsmul⟩
    refine ⟨LinearMap.mk (AddHom.mk f hadd) ?_, rfl⟩
    intro a x
    exact hsmul a x

/-- **模同态的外延性**：两个模同态相等当且仅当它们在每个元素上取值相同。`LinearMap R M N` 是
语义一致的正式承载，`LinearMap.ext` 给出该外延性原理。
> **Entry**: commutative-algebra.module.definition-/
theorem linearMap_ext_iff {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] {F G : M →ₗ[R] N} : F = G ↔ ∀ x, F x = G x :=
  ⟨fun h x => by rw [h], fun h => LinearMap.ext h⟩

/-- **模同态保持零元**：`F 0 = 0`。教材把它列为同态条件之一，在 Lean 里它是 `LinearMap` 的
`AddMonoidHomClass` 实例给出的派生性质（`F.map_zero`，证明走 `F 0 = F (0 • 0) = 0 • F 0 = 0`），
不需要单独假设；`LinearMap` 的父结构 `AddHom` 本身不含零元字段，所以用 `LinearMap.mk` 构造时
也无须给出（多写一个 `map_zero'` 字段会被编译器拒绝）。
> **Entry**: commutative-algebra.module.definition-/
theorem linearMap_map_zero {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (F : M →ₗ[R] N) : F 0 = 0 :=
  F.map_zero

/-- **核的成员刻画**（Atiyah–Macdonald 第 2 章）：`x` 属于 `F` 的核当且仅当 `F x = 0`。
`LinearMap.ker F` 的类型是 `Submodule R M`——这是子模承载在 Mathlib 里的真实上层使用者。
> **Entry**: commutative-algebra.module.definition-/
theorem linearMap_mem_ker_iff {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (F : M →ₗ[R] N) (x : M) :
    x ∈ LinearMap.ker F ↔ F x = 0 :=
  LinearMap.mem_ker

/-- **像的成员刻画**（Atiyah–Macdonald 第 2 章）：`y` 属于 `F` 的像当且仅当存在原像。
`LinearMap.range F` 的类型是 `Submodule R N`，`LinearMap.mem_range` 需要
`RingHomSurjective (RingHom.id R)`，该实例对恒等环同态自动合成。
> **Entry**: commutative-algebra.module.definition-/
theorem linearMap_mem_range_iff {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (F : M →ₗ[R] N) (y : N) :
    y ∈ LinearMap.range F ↔ ∃ x, F x = y :=
  LinearMap.mem_range

/-- **L1 桥**：本库 L1 的教材谓词 `IsSubspace K W`（非空、加法封闭、数乘封闭）与 Mathlib 的
正式承载 `Submodule K V` 等价。`IsSubspace` 是本库 L1 的语义一致的教材记号，`Submodule` 是
Mathlib 的正式承载，本定理是两者之间的桥：正向由「非空 + 数乘封闭 ⟹ 0 ∈ W」补出零元，
再套本文件的 `submodule_of_closure`；反向由 `Submodule` 的三条封闭性回填 `IsSubspace`。
> **Entry**: commutative-algebra.module.definition-/
theorem isSubspace_iff_exists_submodule {K V : Type*} [Field K] [AddCommGroup V]
    [LinearSpace K V] (W : Set V) :
    IsSubspace K W ↔ ∃ S : Submodule K V, (S : Set V) = W := by
  constructor
  · rintro ⟨⟨v0, hv0⟩, hadd, hsmul⟩
    have h0 : (0 : V) ∈ W := by
      have h : (0 : K) • v0 ∈ W := hsmul (0 : K) hv0
      simpa using h
    exact submodule_of_closure h0 (fun x hx y hy => hadd hx hy) (fun a x hx => hsmul a hx)
  · rintro ⟨S, rfl⟩
    refine ⟨⟨0, S.zero_mem⟩, ?_, ?_⟩
    · rintro _ hx _ hy
      exact S.add_mem hx hy
    · rintro c _ hx
      exact S.smul_mem c hx

/-- **A2 桥**：本库 A2 的教材谓词 `TwoSidedIdealSet I`（左理想 ∧ 右理想，零元、加法、负元、
双侧吸收逐条写出）与 Mathlib 的正式承载 `Submodule R R` 等价。`TwoSidedIdealSet` 是本库 A2 的
语义一致的教材记号（交换环中左右两侧吸收等价），`Submodule R R` 是 Mathlib 的正式承载，
本定理是两者之间的桥：正向复用 `submodule_of_closure`（正则模的数量乘即环乘法）；反向的负元由
`(-1 : R) • x` 给出，右吸收在交换环里用 `mul_comm` 把 `r * x` 换成 `x * r`。
> **Entry**: commutative-algebra.module.definition-/
theorem twoSidedIdealSet_iff_exists_submodule_self {R : Type*} [CommRing R] (I : Set R) :
    AbstractAlgebra.Ring.TwoSidedIdealSet I ↔ ∃ S : Submodule R R, (S : Set R) = I := by
  constructor
  · intro hI
    exact submodule_of_closure hI.1.1 (fun x hx y hy => hI.1.2.1 hx hy)
      (fun a x hx => by simpa [smul_eq_mul] using hI.1.2.2.2 a hx)
  · rintro ⟨S, rfl⟩
    constructor
    · refine ⟨S.zero_mem, (fun {_ _} hx hy => S.add_mem hx hy), ?_,
        (fun r {_x} hx => by simpa [smul_eq_mul] using S.smul_mem r hx)⟩
      intro x hx
      simpa [neg_one_smul] using S.smul_mem (-1 : R) hx
    · refine ⟨S.zero_mem, (fun {_ _} hx hy => S.add_mem hx hy), ?_, ?_⟩
      · intro x hx
        simpa [neg_one_smul] using S.smul_mem (-1 : R) hx
      · intro r x hx
        have h : r • x ∈ S := S.smul_mem r hx
        rwa [smul_eq_mul, mul_comm] at h

end CommutativeAlgebra.Module

end SandronesLibrary
