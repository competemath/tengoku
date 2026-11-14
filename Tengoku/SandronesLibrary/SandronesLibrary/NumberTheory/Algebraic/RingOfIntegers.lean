/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.NumberTheory.NumberField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 数域的整数环

本文件给出 N2.3 的教材接口。数域 `K` 的**整数环**（ring of integers）是 `K` 中在 `ℤ` 上整的
全体元素；教材常记作 `𝓞_K`。它是一个整环，以 `K` 为分式域，并且在 `K` 中整闭；作为 `ℤ`-模
它是有限秩自由模，秩等于 `[K : ℚ]`。

Lean 中的正式承载是 `NumberField.RingOfIntegers K`，也就是 `ℤ` 在 `K` 中的整闭包
`integralClosure ℤ K`。它与教材定义一致，因此本文件不另建定义，只给出成员刻画、强制转换、
以及整数环的整闭性、分式域与秩等教材性质。

## 本文件条目

* `number-theory.algebraic.ring-of-integers`
-/

namespace SandronesLibrary.NumberTheory.Algebraic

/-- **整数环的成员刻画。** `K` 中的元素 `x` 在 `ℤ` 上整，当且仅当它来自整数环
`NumberField.RingOfIntegers K` 中的某个元素。

这就是「`𝓞_K` 是 `K` 中在 `ℤ` 上整的元素集合」的精确形式；它把整数环这一子类型与
`N2.2` 的整元素谓词 `IsIntegral ℤ` 桥接起来。

> **Entry**: number-theory.algebraic.ring-of-integers
@isnad1 id=iff.0h2v.s6.eceff019e93d from=translated src=- shape=a0f8a63e vocab=8ceb1e0c
-/
theorem ringOfIntegers_mem_iff (K : Type*) [Field K] {x : K} :
    IsIntegral ℤ x ↔ ∃ y : NumberField.RingOfIntegers K, (algebraMap _ K) y = x :=
  IsIntegralClosure.isIntegral_iff

/-- **由整元素构造整数环元素。** 给定 `x : K` 及其在 `ℤ` 上的整性证明，得到整数环中的元素
`⟨x, hx⟩`。这是读者在 `K` 一侧操作 `𝓞_K` 时最直接的构造入口。

> **Entry**: number-theory.algebraic.ring-of-integers-/
def ringOfIntegersMk (K : Type*) [Field K] (x : K) (hx : IsIntegral ℤ x) :
    NumberField.RingOfIntegers K :=
  ⟨x, hx⟩

/-- 上述构造返回的元素强制转换回 `K` 后就是原来的 `x`。

> **Entry**: number-theory.algebraic.ring-of-integers
@isnad1 id=eq.1h2v.s5.0c377d8aee88 from=translated src=- shape=44ac0884 vocab=8a6a7b64
-/
theorem ringOfIntegersMk_coe (K : Type*) [Field K] (x : K) (hx : IsIntegral ℤ x) :
    ((ringOfIntegersMk K x hx : NumberField.RingOfIntegers K) : K) = x :=
  rfl

/-- **整数环元素在 `K` 中是整的。** 对整数环中的任意元素 `x`，其像在 `ℤ` 上整；这正是
整数环的定义性质的方向之一。

> **Entry**: number-theory.algebraic.ring-of-integers
@isnad1 id=isintegr.0h2v.s4.9ae55edc61be from=translated src=- shape=06ca3aa5 vocab=5353c3fe
-/
theorem ringOfIntegers_isIntegral (K : Type*) [Field K] (x : NumberField.RingOfIntegers K) :
    IsIntegral ℤ (x : K) :=
  NumberField.RingOfIntegers.isIntegral_coe x

/-- **整数环到 `K` 的嵌入是单射。** 整数环作为 `K` 的子环，其强制转换没有核；这使得整数环
可以看作 `K` 的乘法子集，也是后面范数、迹和理想讨论的基础。

> **Entry**: number-theory.algebraic.ring-of-integers
@isnad1 id=injectiv.0h1v.s3.710aa9c8679a from=translated src=- shape=e7497ca1 vocab=978eff34
-/
theorem ringOfIntegers_coe_injective (K : Type*) [Field K] :
    Function.Injective ((↑) : NumberField.RingOfIntegers K → K) :=
  NumberField.RingOfIntegers.coe_injective

/-- **整数环是 `ℤ` 在 `K` 中的整闭包。** 这是一个性质命题：`NumberField.RingOfIntegers K`
恰好是 `ℤ` 在 `K` 中的整闭包，即每个在 `ℤ` 上整的元素都被包含，且每个元素都在 `ℤ` 上整。

> **Entry**: number-theory.algebraic.ring-of-integers
@isnad1 id=isintegr.0h1v.s5.4893ab337797 from=translated src=- shape=3c32ce15 vocab=0156874b
-/
theorem ringOfIntegers_isIntegralClosure (K : Type*) [Field K] :
    IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K :=
  inferInstance

/-- **数域的整数环以该数域为分式域。** 对 `NumberField K`，`K` 是 `𝓞_K` 的分式域；这正是
教材中「整数环的分式域回到原数域」的表述。

> **Entry**: number-theory.algebraic.ring-of-integers
@isnad1 id=isfracti.0h1v.s4.b9446b02f3d7 from=translated src=- shape=338784ee vocab=af25e3a5
-/
theorem ringOfIntegers_isFractionRing (K : Type*) [Field K] [NumberField K] :
    IsFractionRing (NumberField.RingOfIntegers K) K :=
  inferInstance

/-- **数域的整数环是整闭的。** `𝓞_K` 在自身分式域 `K` 中整闭：`K` 中在 `𝓞_K` 上整的元素
已经属于 `𝓞_K`。这是整数环最重要的结构性质之一，也是后续 Dedekind 性讨论的前提。

> **Entry**: number-theory.algebraic.ring-of-integers
@isnad1 id=isintegr.0h1v.s4.20d6d66d8e90 from=translated src=- shape=9499e9bc vocab=5dd64ac2
-/
theorem ringOfIntegers_isIntegrallyClosed (K : Type*) [Field K] [NumberField K] :
    IsIntegrallyClosed (NumberField.RingOfIntegers K) :=
  inferInstance

/-- **整数环的秩。** 作为 `ℤ`-模，整数环 `𝓞_K` 的秩（有限维自由模的维数）等于数域 `K`
作为 `ℚ`-向量空间的维数，即扩张次数 `[K : ℚ]`。

这是教材中「`𝓞_K` 是秩为 `[K : ℚ]` 的自由 `ℤ`-模，其基称为整基」的秩部分；本条目只给出
秩相等，整基的存在与具体构造留待后续批次。

> **Entry**: number-theory.algebraic.ring-of-integers
@isnad1 id=eq.0h1v.s6.e2828a4890bb from=translated src=- shape=9c43e60b vocab=1be805cc
-/
theorem ringOfIntegers_rank (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℤ (NumberField.RingOfIntegers K) = Module.finrank ℚ K :=
  NumberField.RingOfIntegers.rank K

end SandronesLibrary.NumberTheory.Algebraic
