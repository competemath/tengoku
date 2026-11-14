/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.CommutativeAlgebra.Module.Definition
import Tengoku.SandronesLibrary.SandronesLibrary.CommutativeAlgebra.Module.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# CommutativeAlgebra / Module —— 模的三大同构定理（Atiyah–Macdonald 第 2 章）

本文件承载条目 **commutative-algebra.module.isomorphism-theorems**（CA1 定义层）。

三条定理的教材陈述（`S, T` 是 `M` 的子模，`f : M → N` 是模同态）：

* **第一同构定理**：`M / ker f ≅ im f`；`f` 满射时 `M / ker f ≅ N`。
* **第二同构定理**：`(S + T) / T ≅ S / (S ∩ T)`。
* **第三同构定理**：若 `S ≤ T`，则 `(M / S) / (T / S) ≅ M / T`。

**证明链口径**（本条目与「包装 Mathlib 结论」的区别所在）：三条定理都按
「构造诱导映射 → 证核/单射 → 证满射 → 用 `LinearEquiv.ofBijective` 组装」四步自己走完。
Mathlib 里已有 `LinearMap.quotKerEquivRange`、`LinearMap.quotientInfEquivSupQuotient`、
`Submodule.quotientQuotientEquivQuotient` 三条现成等价，本文件**不引用它们**，也不引用
`Submodule.quotientQuotientEquivQuotientAux`；只复用下层接口（`liftQ`、`mkQ`、`factor`、
`ker_liftQ_eq_bot`、`Submodule.Quotient.eq` 等）。

**陈述口径**：第二同构定理里 `S ∩ T` 必须看成 `S` 的子模，Lean 的写法是
`Submodule.comap S.subtype T`（`x : ↥S` 满足 `(x : M) ∈ T`）；`S + T` 写成 `S ⊔ T`。
本文件给出 `second_iso_mem_comap_iff` 把这两种写法翻译清楚。

公开陈述一律写在 Atiyah–Macdonald 的设定 `[CommRing R] [AddCommGroup M]` 上。
-/

namespace SandronesLibrary

namespace CommutativeAlgebra.Module

/-! ## 一、第一同构定理：`M / ker f ≅ im f` -/

/-- **第一同构定理的诱导映射**：`f` 诱导出 `M ⧸ ker f →ₗ[R] im f`，在陪集上取
`mk x ↦ f x`（把 `f x` 看作 `im f` 的元素）。构造用商模泛性质 `Submodule.liftQ`，
配合 `LinearMap.codRestrict` 把余域收到 `im f`。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
noncomputable def firstIsoHom {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    M ⧸ LinearMap.ker f →ₗ[R] LinearMap.range f :=
  LinearMap.codRestrict (LinearMap.range f) ((LinearMap.ker f).liftQ f le_rfl)
    (fun x => Submodule.Quotient.induction_on (LinearMap.ker f) x fun m =>
      ⟨m, (Submodule.liftQ_apply (LinearMap.ker f) f m).symm⟩)

/-- **第一同构定理诱导映射在陪集上的取值**：`firstIsoHom f (mk x) = f x`。
这是教材里 `x + ker f ↦ f(x)` 的精确形式。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem firstIsoHom_mk {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (x : M) :
    firstIsoHom f (Submodule.Quotient.mk x) = ⟨f x, ⟨x, rfl⟩⟩ :=
  Subtype.ext (Submodule.liftQ_apply (LinearMap.ker f) f x)

/-- **第一同构定理诱导映射的核**：`ker (firstIsoHom f) = ⊥`。教材的证明是「`f(x) = 0` 当且仅当
`x ∈ ker f`，而后者当且仅当 `x + ker f` 是零陪集」；这条等价正是单射性的全部内容。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem firstIsoHom_ker {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) : LinearMap.ker (firstIsoHom f) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  revert hx
  refine Submodule.Quotient.induction_on (LinearMap.ker f) x fun m hx => ?_
  rw [LinearMap.mem_ker, firstIsoHom_mk] at hx
  have hm : f m = 0 := congrArg Subtype.val hx
  rw [Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_ker.mpr hm

/-- **第一同构定理诱导映射是单射**。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem firstIsoHom_injective {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) : Function.Injective (firstIsoHom f) :=
  LinearMap.ker_eq_bot.mp (firstIsoHom_ker f)

/-- **第一同构定理诱导映射是满射**：`im f` 的每个元素都是某个 `f x`，而 `f x` 就是陪集
`x + ker f` 的像。这是教材「满射」那一半的证明链。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem firstIsoHom_surjective {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) : Function.Surjective (firstIsoHom f) := by
  rintro ⟨y, x, rfl⟩
  exact ⟨Submodule.Quotient.mk x, Subtype.ext rfl⟩

/-- **第一同构定理**：`M ⧸ ker f ≃ₗ[R] im f`。由上面「核为 `⊥`（单射）」与「满射」两条，
经 `LinearEquiv.ofBijective` 组装。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
noncomputable def first_iso {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  LinearEquiv.ofBijective (firstIsoHom f) ⟨firstIsoHom_injective f, firstIsoHom_surjective f⟩

/-- **第一同构定理（满射版本）**：若 `f` 满射，则 `M ⧸ ker f ≃ₗ[R] N`。
教材里最常用的是这一形式（例如「环作为自身模商掉理想的核」）。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
noncomputable def first_iso_of_surjective {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : (M ⧸ LinearMap.ker f) ≃ₗ[R] N :=
  (first_iso f).trans (LinearEquiv.ofTop (LinearMap.range f) (LinearMap.range_eq_top.mpr hf))

/-- **第一同构定理在陪集上的取值**：`first_iso f (mk x)` 的底层元素就是 `f x`。
教材用它做具体计算；本定理让「同构」不只是存在性，而是可以逐点求值。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem first_iso_mk {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (x : M) :
    (first_iso f (Submodule.Quotient.mk x) : N) = f x :=
  congrArg Subtype.val (firstIsoHom_mk f x)

/-! ## 二、第二同构定理：`(S ⊔ T) / T ≅ S / (S ⊓ T)` -/

/-- **第二同构定理的诱导映射**：`S → (S ⊔ T) ⧸ T`，`x ↦ x + T`。先由包含
`S ↪ S ⊔ T`（`Submodule.inclusion`）与自然投影复合，再把 `T` 拉回到 `S` 上。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
noncomputable def secondIsoHom {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) :
    ↥S →ₗ[R] (↥(S ⊔ T)) ⧸ Submodule.comap (S ⊔ T).subtype T :=
  (Submodule.comap (S ⊔ T).subtype T).mkQ.comp (Submodule.inclusion le_sup_left)

/-- **第二同构定理诱导映射的核**：`ker = S ∩ T`（写成 `comap S.subtype T`）。
教材的证明是「`x ∈ S` 的陪集 `x + T` 为零，当且仅当 `x ∈ T`，即 `x ∈ S ∩ T`」。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem secondIsoHom_ker {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) :
    LinearMap.ker (secondIsoHom S T) = Submodule.comap S.subtype T := by
  ext x
  simp only [LinearMap.mem_ker, secondIsoHom, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_inclusion,
    Submodule.subtype_apply]

/-- **`S ∩ T` 在 `↥S` 中的写法**：`x : ↥S` 属于 `comap S.subtype T` 当且仅当它作为 `M` 的元素
属于 `S ⊓ T`。这条桥让教材记号 `S ∩ T` 与 Lean 的 `comap S.subtype T` 可以互相翻译。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem second_iso_mem_comap_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) (x : ↥S) :
    x ∈ Submodule.comap S.subtype T ↔ (x : M) ∈ S ⊓ T := by
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

/-- **第二同构定理的商映射**：把 `secondIsoHom` 用商模泛性质下降为
`S ⧸ (S ⊓ T) →ₗ[R] (S ⊔ T) ⧸ T`。下降的合法性由 `secondIsoHom_ker` 给出。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
noncomputable def secondIsoMap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) :
    (↥S ⧸ Submodule.comap S.subtype T) →ₗ[R]
      (↥(S ⊔ T)) ⧸ Submodule.comap (S ⊔ T).subtype T :=
  (Submodule.comap S.subtype T).liftQ (secondIsoHom S T)
    (le_of_eq (secondIsoHom_ker S T).symm)

/-- **第二同构定理的商映射是单射**：核为 `⊥`。教材的读法是「`x + (S ∩ T)` 与 `x' + (S ∩ T)`
在 `(S + T)/T` 中有相同像 ⟹ `x - x' ∈ T`，而 `x - x' ∈ S`，故 `x - x' ∈ S ∩ T`」。
Lean 侧走 `Submodule.ker_liftQ_eq_bot`：因为 `ker (secondIsoHom S T) = S ⊓ T` 恰好等于被商的子模。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem secondIsoMap_ker {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) : LinearMap.ker (secondIsoMap S T) = ⊥ :=
  Submodule.ker_liftQ_eq_bot (Submodule.comap S.subtype T) (secondIsoHom S T) _
    (le_of_eq (secondIsoHom_ker S T))

/-- **第二同构定理的商映射是满射**：`(S + T)/T` 的任一元素可写成 `x + T`（`x ∈ S + T`）；
把 `x` 拆成 `s + t`（`s ∈ S`，`t ∈ T`），则 `x + T = s + T`，落在 `s + (S ∩ T)` 的像上。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem secondIsoMap_surjective {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) : Function.Surjective (secondIsoMap S T) := by
  intro y
  refine Submodule.Quotient.induction_on (Submodule.comap (S ⊔ T).subtype T) y ?_
  intro x
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp x.2
  refine ⟨Submodule.Quotient.mk ⟨s, hs⟩, ?_⟩
  rw [secondIsoMap, Submodule.liftQ_apply, secondIsoHom, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.inclusion_apply, Submodule.Quotient.eq]
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]
  have hx : (x : M) = s + t := hst.symm
  rw [hx]
  have hsub : s - (s + t) = -t := by abel
  rw [hsub]
  exact Submodule.neg_mem _ ht

/-- **第二同构定理**：`(S ⊔ T) ⧸ T ≃ₗ[R] S ⧸ (S ⊓ T)`（教材写作 `(S+T)/T ≅ S/(S∩T)`）。
由单射与满射两条经 `LinearEquiv.ofBijective` 组装。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
noncomputable def second_iso {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) :
    (↥S ⧸ Submodule.comap S.subtype T) ≃ₗ[R]
      (↥(S ⊔ T)) ⧸ Submodule.comap (S ⊔ T).subtype T :=
  LinearEquiv.ofBijective (secondIsoMap S T)
    ⟨LinearMap.ker_eq_bot.mp (secondIsoMap_ker S T), secondIsoMap_surjective S T⟩

/-- **第二同构定理在陪集上的取值**：`second_iso S T (mk x) = mk (inclusion x)`，
即 `x + (S ∩ T) ↦ x + T`。教材用它把同构写成可计算的形式。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem second_iso_mk {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) (x : ↥S) :
    second_iso S T (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion le_sup_left x) := by
  change secondIsoMap S T (Submodule.Quotient.mk x) = _
  rw [secondIsoMap, Submodule.liftQ_apply, secondIsoHom, LinearMap.comp_apply,
    Submodule.mkQ_apply]

/-! ## 三、第三同构定理：`(M ⧸ S) ⧸ (T ⧸ S) ≅ M ⧸ T`（`S ≤ T`） -/

/-- **第三同构定理的核计算**：`S ≤ T` 时商映射 `M ⧸ S →ₗ[R] M ⧸ T` 的核恰是 `T` 在 `M ⧸ S` 中的
像 `T.map S.mkQ`（教材写作 `T/S`）。正向：`x + S` 落到零陪集即 `x ∈ T`；反向：若 `x - t ∈ S`
（`t ∈ T`）则由 `S ≤ T` 得 `x ∈ T`。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem factor_ker {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {S T : Submodule R M} (h : S ≤ T) :
    LinearMap.ker (Submodule.factor h) = T.map S.mkQ := by
  ext x
  refine Submodule.Quotient.induction_on S x fun m => ?_
  change (Submodule.factor h) (S.mkQ m) = 0 ↔ S.mkQ m ∈ T.map S.mkQ
  rw [Submodule.factor_mk, Submodule.mem_map]
  constructor
  · intro hm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hm
    exact ⟨m, hm, rfl⟩
  · rintro ⟨t, ht, htm⟩
    have h1 : t - m ∈ S := (Submodule.Quotient.eq S).mp htm
    have h2 : t - m ∈ T := h h1
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hm : m = t - (t - m) := by abel
    rw [hm]
    exact Submodule.sub_mem T ht h2

/-- **第三同构定理的商映射**：把 `M ⧸ S →ₗ[R] M ⧸ T` 用商模泛性质下降为
`(M ⧸ S) ⧸ (T ⧸ S) →ₗ[R] M ⧸ T`。下降的合法性由 `factor_ker` 给出。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
noncomputable def thirdIsoMap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {S T : Submodule R M} (h : S ≤ T) :
    (M ⧸ S) ⧸ T.map S.mkQ →ₗ[R] M ⧸ T :=
  (T.map S.mkQ).liftQ (Submodule.factor h) (le_of_eq (factor_ker h).symm)

/-- **第三同构定理的商映射是单射**：核为 `⊥`，由 `factor_ker` 与
`Submodule.ker_liftQ_eq_bot` 直接给出——「被商的子模恰好是核」正是单射性的全部内容。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem thirdIsoMap_ker {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {S T : Submodule R M} (h : S ≤ T) : LinearMap.ker (thirdIsoMap h) = ⊥ :=
  Submodule.ker_liftQ_eq_bot (T.map S.mkQ) (Submodule.factor h) _ (le_of_eq (factor_ker h))

/-- **第三同构定理的商映射是满射**：`M ⧸ T` 的元素是 `x + T`，而它就是双重陪集
`(x + S) + (T/S)` 的像。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem thirdIsoMap_surjective {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {S T : Submodule R M} (h : S ≤ T) : Function.Surjective (thirdIsoMap h) := by
  intro y
  refine Submodule.Quotient.induction_on T y fun m => ?_
  exact ⟨Submodule.Quotient.mk (S.mkQ m), by
    rw [thirdIsoMap, Submodule.liftQ_apply, Submodule.factor_mk, Submodule.mkQ_apply]⟩

/-- **第三同构定理**：若 `S ≤ T`，则 `(M ⧸ S) ⧸ (T ⧸ S) ≃ₗ[R] M ⧸ T`
（教材写作 `(M/S)/(T/S) ≅ M/T`）。由单射与满射两条经 `LinearEquiv.ofBijective` 组装。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
noncomputable def third_iso {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {S T : Submodule R M} (h : S ≤ T) : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ T :=
  LinearEquiv.ofBijective (thirdIsoMap h)
    ⟨LinearMap.ker_eq_bot.mp (thirdIsoMap_ker h), thirdIsoMap_surjective h⟩

/-- **第三同构定理在双重陪集上的取值**：`third_iso h (mk (mk x)) = mk x`，
即 `(x + S) + (T/S) ↦ x + T`。
> **Entry**: commutative-algebra.module.isomorphism-theorems-/
theorem third_iso_mk_mk {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {S T : Submodule R M} (h : S ≤ T) (x : M) :
    third_iso h (Submodule.Quotient.mk (S.mkQ x)) = Submodule.Quotient.mk x := by
  change thirdIsoMap h (Submodule.Quotient.mk (S.mkQ x)) = Submodule.Quotient.mk x
  rw [thirdIsoMap, Submodule.liftQ_apply, Submodule.factor_mk, Submodule.mkQ_apply]

end CommutativeAlgebra.Module

end SandronesLibrary
