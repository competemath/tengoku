/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# AbstractAlgebra / RingQuotient —— 双边理想的商环构造

本文件当前条目：

* **abstract-algebra.ring.quotient**：由双边理想定义同余关系与商集合；在商集合上下降
  `0, 1, +, *, -`，证明环公理；构造商映射、计算其核，并证明商环泛性质。

数学边界：本模块只处理带单位的（不必交换的）Mathlib `Ring`，因此乘法下降要求
`TwoSidedIdealSet`。商环由 `Quotient` 显式承载，公开结论使用本库的 `RingAxioms`、
`RingHomomorphism` 与普通函数；这里不引入 `Module`，也不把商环打包成 Mathlib 的
`Ideal.Quotient`。泛性质的输入是假设同态在 `I` 上为零，并给出唯一的普通函数提升。
-/

namespace SandronesLibrary.AbstractAlgebra.Ring

/-- **理想同余关系**：两个环元素 `x,y` 关于集合 `I` 同余，当且仅当差 `x-y` 属于
`I`。此定义只负责给出关系；其等价性及与运算的相容性需要 `I` 是双边理想。
> **Entry**: abstract-algebra.ring.quotient-/
def idealCongruent {R : Type*} [Sub R] (I : Set R) (x y : R) : Prop :=
  x - y ∈ I

/-- 若 `I` 满足本库双边理想判据，则“差属于 `I`”是 `R` 上的等价关系：零元给出
自反性，取负给出对称性，加法封闭给出传递性。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=equivale.1h2v.s5.0fe97ff17d4d from=translated src=- shape=b161458b vocab=f4cf9442
-/
theorem idealCongruent_equivalence {R : Type*} [Ring R] {I : Set R}
    (hI : TwoSidedIdealSet I) : Equivalence (idealCongruent I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simpa [idealCongruent] using hI.1.1
  · intro x y hxy
    have hneg : -(x - y) ∈ I := hI.1.2.2.1 hxy
    simpa [idealCongruent] using hneg
  · intro x y z hxy hyz
    have hadd : (x - y) + (y - z) ∈ I := hI.1.2.1 hxy hyz
    simpa [idealCongruent] using hadd

/-- 把双边理想 `I` 所定义的理想同余关系及其等价性证明打包为 Lean 的 `Setoid R`，
供后续 `Quotient` 构造使用。
> **Entry**: abstract-algebra.ring.quotient-/
def idealCongruenceSetoid {R : Type*} [Ring R] {I : Set R}
    (hI : TwoSidedIdealSet I) : Setoid R :=
  ⟨idealCongruent I, idealCongruent_equivalence hI⟩

/-- **商环的底层集合**：将 `R` 按双边理想 `I` 给出的理想同余关系取商。此处仅构造
类型；环运算与环公理在下文分别下降和验证。
> **Entry**: abstract-algebra.ring.quotient-/
def quotientRingSet {R : Type*} [Ring R] (I : Set R) (hI : TwoSidedIdealSet I) :=
  Quotient (idealCongruenceSetoid hI)

/-- **商投影**：把 `x : R` 送到它在 `R/I` 中的等价类。该函数是底层集合之间的普通
函数，其保持环运算的性质在环结构构造完成后证明。
> **Entry**: abstract-algebra.ring.quotient-/
def quotientRingProjection {R : Type*} [Ring R] (I : Set R) (hI : TwoSidedIdealSet I) :
    R → quotientRingSet I hI :=
  Quotient.mk _

/-- 两个元素经商投影后相等，当且仅当它们关于 `I` 理想同余，即 `x-y ∈ I`。这是
商环中等式的基本判定准则。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=iff.1h4v.s6.98fbe14e6a1f from=translated src=- shape=0f063016 vocab=2c3b26fa
-/
theorem quotientRingProjection_eq_iff {R : Type*} [Ring R] {I : Set R}
    (hI : TwoSidedIdealSet I) (x y : R) :
    quotientRingProjection I hI x = quotientRingProjection I hI y ↔ idealCongruent I x y := by
  exact Quotient.eq

/-- 理想同余与加法相容：若 `a ≡ a'` 且 `b ≡ b'` 模 `I`，则
`a+b ≡ a'+b'` 模 `I`。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=idealcon.3h6v.s6.10b97e6943e9 from=translated src=- shape=e6300839 vocab=767c7035
-/
theorem idealCongruent_add {R : Type*} [Ring R] {I : Set R}
    (hI : TwoSidedIdealSet I) {a a' b b' : R}
    (ha : idealCongruent I a a') (hb : idealCongruent I b b') :
    idealCongruent I (a + b) (a' + b') := by
  have hadd : (a - a') + (b - b') ∈ I := hI.1.2.1 ha hb
  change a + b - (a' + b') ∈ I
  convert hadd using 1
  all_goals noncomm_ring

/-- 理想同余与乘法相容：双边吸收性分别控制乘积差的左右两项，从而代表元的乘积
给出良定义的商类。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=idealcon.3h6v.s6.e10b41ee1858 from=translated src=- shape=e6300839 vocab=bfabeee2
-/
theorem idealCongruent_mul {R : Type*} [Ring R] {I : Set R}
    (hI : TwoSidedIdealSet I) {a a' b b' : R}
    (ha : idealCongruent I a a') (hb : idealCongruent I b b') :
    idealCongruent I (a * b) (a' * b') := by
  have hright : (a - a') * b ∈ I := hI.2.2.2.2 b ha
  have hleft : a' * (b - b') ∈ I := hI.1.2.2.2 a' hb
  have hadd := hI.1.2.1 hright hleft
  change a * b - a' * b' ∈ I
  convert hadd using 1
  all_goals noncomm_ring

/-- 理想同余与取负相容：`a-b ∈ I` 蕴含其负元属于 `I`，故 `-a ≡ -b` 模 `I`。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=idealcon.2h4v.s6.95faef6da4a5 from=translated src=- shape=6a7d869e vocab=10c0f941
-/
theorem idealCongruent_neg {R : Type*} [Ring R] {I : Set R}
    (hI : TwoSidedIdealSet I) {a b : R} (hab : idealCongruent I a b) :
    idealCongruent I (-a) (-b) := by
  have hneg : -(a - b) ∈ I := hI.1.2.2.1 hab
  change -a - -b ∈ I
  convert hneg using 1
  all_goals noncomm_ring

section Operations

variable {R : Type*} [Ring R] (I : Set R) (hI : TwoSidedIdealSet I)

/-- 商集合上的加法，由代表元加法经 `Quotient.map₂` 下降；良定义性来自
`idealCongruent_add`。
> **Entry**: abstract-algebra.ring.quotient-/
def quotientAdd : quotientRingSet I hI → quotientRingSet I hI → quotientRingSet I hI :=
  Quotient.map₂ (fun a b : R => a + b) (by
    intro a a' ha b b' hb
    exact idealCongruent_add hI ha hb)

/-- 商集合上的乘法，由代表元乘法下降；双边理想条件保证左右改变代表元都不改变结果。
> **Entry**: abstract-algebra.ring.quotient-/
def quotientMul : quotientRingSet I hI → quotientRingSet I hI → quotientRingSet I hI :=
  Quotient.map₂ (fun a b : R => a * b) (by
    intro a a' ha b b' hb
    exact idealCongruent_mul hI ha hb)

/-- 商集合上的加法逆元，由代表元取负下降；其良定义性来自理想对取负封闭。
> **Entry**: abstract-algebra.ring.quotient-/
def quotientNeg : quotientRingSet I hI → quotientRingSet I hI :=
  Quotient.map (fun a : R => -a) (by
    intro a b hab
    exact idealCongruent_neg hI hab)

/-- 商集合的零元是 `R` 中零元的等价类。
> **Entry**: abstract-algebra.ring.quotient-/
def quotientZero : quotientRingSet I hI := quotientRingProjection I hI 0

/-- 商集合的单位元是 `R` 中单位元的等价类。
> **Entry**: abstract-algebra.ring.quotient-/
def quotientOne : quotientRingSet I hI := quotientRingProjection I hI 1

/-- 将下降后的加法注册为商集合的 `Add` 实例。
> **Entry**: abstract-algebra.ring.quotient-/
instance quotientRingSetAdd : Add (quotientRingSet I hI) := ⟨quotientAdd I hI⟩

/-- 将下降后的乘法注册为商集合的 `Mul` 实例。
> **Entry**: abstract-algebra.ring.quotient-/
instance quotientRingSetMul : Mul (quotientRingSet I hI) := ⟨quotientMul I hI⟩

/-- 将下降后的取负运算注册为商集合的 `Neg` 实例。
> **Entry**: abstract-algebra.ring.quotient-/
instance quotientRingSetNeg : Neg (quotientRingSet I hI) := ⟨quotientNeg I hI⟩

/-- 将零元等价类注册为商集合的 `Zero` 实例。
> **Entry**: abstract-algebra.ring.quotient-/
instance quotientRingSetZero : Zero (quotientRingSet I hI) := ⟨quotientZero I hI⟩

/-- 将单位元等价类注册为商集合的 `One` 实例。
> **Entry**: abstract-algebra.ring.quotient-/
instance quotientRingSetOne : One (quotientRingSet I hI) := ⟨quotientOne I hI⟩

/-- 商投影保持加法的计算公式：两个投影类之和等于代表元之和的投影类。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.1h4v.s6.56371f9d7708 from=translated src=- shape=521935bf vocab=10437ca1
-/
@[simp] theorem quotientAdd_projection (a b : R) :
    quotientRingProjection I hI a + quotientRingProjection I hI b =
      quotientRingProjection I hI (a + b) := by
  change quotientAdd I hI (Quotient.mk _ a) (Quotient.mk _ b) = Quotient.mk _ (a + b)
  unfold quotientAdd
  apply Quotient.map₂_mk

/-- 商投影保持乘法的计算公式：两个投影类之积等于代表元之积的投影类。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.1h4v.s6.3b7282f7d317 from=translated src=- shape=521935bf vocab=7b0c7f68
-/
@[simp] theorem quotientMul_projection (a b : R) :
    quotientRingProjection I hI a * quotientRingProjection I hI b =
      quotientRingProjection I hI (a * b) := by
  change quotientMul I hI (Quotient.mk _ a) (Quotient.mk _ b) = Quotient.mk _ (a * b)
  unfold quotientMul
  apply Quotient.map₂_mk

/-- 商投影保持取负的计算公式：投影类的负元就是负代表元的投影类。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.1h3v.s6.30c4d7df28ad from=translated src=- shape=af99af35 vocab=cb826a3b
-/
@[simp] theorem quotientNeg_projection (a : R) :
    -(quotientRingProjection I hI a) = quotientRingProjection I hI (-a) := by
  change quotientNeg I hI (Quotient.mk _ a) = Quotient.mk _ (-a)
  unfold quotientNeg
  apply Quotient.map_mk

/-- 商集合零元按定义等于 `0 : R` 的投影类。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.1h2v.s6.8e395dfc618d from=translated src=- shape=3e90ec3a vocab=dc92c4e0
-/
@[simp] theorem quotientZero_eq_projection :
    (0 : quotientRingSet I hI) = quotientRingProjection I hI 0 := by
  rfl

/-- 商集合单位元按定义等于 `1 : R` 的投影类。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.1h2v.s6.208cabd20532 from=translated src=- shape=3e90ec3a vocab=dc92c4e0
-/
@[simp] theorem quotientOne_eq_projection :
    (1 : quotientRingSet I hI) = quotientRingProjection I hI 1 := by
  rfl

/-- 下降到 `R/I` 的五种运算满足本库逐条列出的全部环公理。证明对商类作归纳，并将
每条等式化归为代表元所在环 `R` 的对应公理。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=ringaxio.1h2v.s6.39b925a2371a from=translated src=- shape=d5b4db11 vocab=089814a0
-/
theorem quotientRingSet_ringAxioms : RingAxioms (quotientRingSet I hI) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    change quotientRingProjection I hI ((a + b) + c) =
      quotientRingProjection I hI (a + (b + c))
    rw [add_assoc]
  · intro x
    refine Quotient.inductionOn x ?_
    intro a
    change quotientRingProjection I hI (0 + a) = quotientRingProjection I hI a
    rw [zero_add]
  · intro x
    refine Quotient.inductionOn x ?_
    intro a
    change quotientRingProjection I hI (a + 0) = quotientRingProjection I hI a
    rw [add_zero]
  · intro x
    refine Quotient.inductionOn x ?_
    intro a
    change quotientRingProjection I hI (-a + a) = quotientRingProjection I hI 0
    rw [neg_add_cancel]
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change quotientRingProjection I hI (a + b) = quotientRingProjection I hI (b + a)
    rw [add_comm]
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    change quotientRingProjection I hI ((a * b) * c) =
      quotientRingProjection I hI (a * (b * c))
    rw [mul_assoc]
  · intro x
    refine Quotient.inductionOn x ?_
    intro a
    change quotientRingProjection I hI (1 * a) = quotientRingProjection I hI a
    rw [one_mul]
  · intro x
    refine Quotient.inductionOn x ?_
    intro a
    change quotientRingProjection I hI (a * 1) = quotientRingProjection I hI a
    rw [mul_one]
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    change quotientRingProjection I hI (a * (b + c)) =
      quotientRingProjection I hI (a * b + a * c)
    rw [mul_add]
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    change quotientRingProjection I hI ((a + b) * c) =
      quotientRingProjection I hI (a * c + b * c)
    rw [add_mul]

/-- 商投影是本库意义下的环同态：它保持零元、单位元、加法、乘法与取负。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=ringhomo.1h2v.s6.11d6cf4b2486 from=translated src=- shape=3d392d3a vocab=2c015092
-/
theorem quotientRingProjection_is_ringHomomorphism :
    RingHomomorphism (quotientRingProjection I hI) := by
  exact ⟨(quotientZero_eq_projection I hI).symm,
    (quotientOne_eq_projection I hI).symm,
    fun x y => (quotientAdd_projection I hI x y).symm,
    fun x y => (quotientMul_projection I hI x y).symm,
    fun x => (quotientNeg_projection I hI x).symm⟩

/-- 商投影的核恰为原双边理想 `I`：元素投影为商环零元，当且仅当该元素属于 `I`。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.1h2v.s6.3f2ae45da3be from=translated src=- shape=15fb9814 vocab=bd123236
-/
theorem quotientRingProjection_kernel :
    {x : R | quotientRingProjection I hI x = 0} = I := by
  ext x
  rw [quotientZero_eq_projection]
  simpa [idealCongruent] using quotientRingProjection_eq_iff hI x 0

end Operations

section UniversalProperty

variable {R S : Type*} [Ring R] [Ring S]
variable (I : Set R) (hI : TwoSidedIdealSet I)
variable (f : R → S) (hf : RingHomomorphism f)
variable (hker : ∀ x : R, x ∈ I → f x = 0)

/-- **商环提升**：若环同态 `f : R → S` 在 `I` 上为零，则它在理想同余类上取值相同，
因而唯一地下降为普通函数 `R/I → S`。参数 `_hf` 与 `_hker` 记录良定义性所需假设。
> **Entry**: abstract-algebra.ring.quotient-/
def quotientRingSetLift (_hf : RingHomomorphism f)
    (_hker : ∀ x : R, x ∈ I → f x = 0) : quotientRingSet I hI → S :=
  Quotient.lift f (by
    intro a b hab
    have hdiff : f (a - b) = 0 := _hker _ hab
    have hmap : f (a - b) = f a - f b := by
      calc
        f (a - b) = f (a + -b) := by rw [sub_eq_add_neg]
        _ = f a + f (-b) := _hf.2.2.1 a (-b)
        _ = f a + -f b := by rw [_hf.2.2.2.2]
        _ = f a - f b := by rw [sub_eq_add_neg]
    have hsub : f a - f b = 0 := hmap.symm.trans hdiff
    exact sub_eq_zero.mp hsub)

/-- 提升函数与商投影组成交换三角：对每个 `x : R`，先投影再提升得到原值 `f x`。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.3h5v.s7.bd038d8feb80 from=translated src=- shape=c7631434 vocab=1c82d190
-/
@[simp] theorem quotientRingSetLift_projection (x : R) :
    quotientRingSetLift I hI f hf hker (quotientRingProjection I hI x) = f x := by
  unfold quotientRingSetLift quotientRingProjection
  apply Quotient.lift_mk

/-- 商环提升保持零元、单位元、加法、乘法和取负，因而是本库意义下的环同态。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=ringhomo.3h4v.s7.95e5dcf25c88 from=translated src=- shape=f22a9313 vocab=d2616e20
-/
theorem quotientRingSetLift_is_ringHomomorphism :
    RingHomomorphism (quotientRingSetLift I hI f hf hker) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change f 0 = 0
    exact hf.1
  · change f 1 = 1
    exact hf.2.1
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change f (a + b) = f a + f b
    exact hf.2.2.1 a b
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change f (a * b) = f a * f b
    exact hf.2.2.2.1 a b
  · intro x
    refine Quotient.inductionOn x ?_
    intro a
    change f (-a) = -(f a)
    exact hf.2.2.2.2 a

/-- 提升的逐点唯一性：任意函数 `g : R/I → S` 只要在所有投影类上等于 `f`，就必然
等于规范提升；这里不额外要求 `g` 已被证明为环同态。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.4h5v.s7.10267b120a70 from=translated src=- shape=8e473eb7 vocab=9a083aa3
-/
theorem quotientRingSetLift_pointwise_unique (g : quotientRingSet I hI → S)
    (htriangle : ∀ x : R, g (quotientRingProjection I hI x) = f x) :
    g = quotientRingSetLift I hI f hf hker := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  exact htriangle x

/-- 商环同态提升的唯一性版本：若环同态 `g` 与商投影的复合等于 `f`，则 `g` 等于
规范提升。参数 `_hg` 明示候选函数是环同态，唯一性本身由投影类覆盖商集得到。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=eq.5h5v.s8.f9fb5876389e from=translated src=- shape=e9174aa7 vocab=9a083aa3
-/
theorem quotientRingSetLift_unique (g : quotientRingSet I hI → S)
    (_hg : RingHomomorphism g)
    (htriangle : ∀ x : R, g (quotientRingProjection I hI x) = f x) :
    g = quotientRingSetLift I hI f hf hker := by
  exact quotientRingSetLift_pointwise_unique I hI f hf hker g htriangle

include hf hker
/-- **商环泛性质**：每个在双边理想 `I` 上为零的环同态 `f : R → S`，唯一分解为
商投影 `R → R/I` 后接一个本库意义下的环同态 `R/I → S`。
> **Entry**: abstract-algebra.ring.quotient
@isnad1 id=existsun.3h4v.s8.7391768fbb4a from=translated src=- shape=962bb04f vocab=08090856
-/
theorem quotientRingSet_universal_property :
    ∃! g : quotientRingSet I hI → S,
      RingHomomorphism g ∧
        ∀ x : R, g (quotientRingProjection I hI x) = f x := by
  refine ⟨quotientRingSetLift I hI f hf hker, ?_, ?_⟩
  · exact ⟨quotientRingSetLift_is_ringHomomorphism I hI f hf hker,
      quotientRingSetLift_projection I hI f hf hker⟩
  · intro g hg
    exact quotientRingSetLift_unique I hI f hf hker g hg.1 hg.2

end UniversalProperty

end SandronesLibrary.AbstractAlgebra.Ring
