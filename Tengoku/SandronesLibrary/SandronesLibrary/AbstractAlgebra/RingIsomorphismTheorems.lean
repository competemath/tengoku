/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.RingQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 环同构定理

本模块从普通函数和本库 `RingHomomorphism` 的逐项教材谓词出发，打包双边理想、核与像，
并在显式商环 `quotientRingSet` 上证明同构定理。环同构本身以语义一致的 Mathlib
`RingEquiv` 为正式承载；历史 `RingIsomorphism` 只保留为无损兼容层。
-/

namespace SandronesLibrary.AbstractAlgebra.Ring

/-- **环同构**：一对互逆普通函数，且两个方向都满足本库环同态谓词。
> **Entry**: abstract-algebra.ring.iso-theorems-/
structure RingIsomorphism (R S : Type*) [Ring R] [Ring S] where
  toFun : R → S
  inverse : S → R
  left_inverse : ∀ x : R, inverse (toFun x) = x
  right_inverse : ∀ y : S, toFun (inverse y) = y
  toFun_is_ringHomomorphism : RingHomomorphism toFun
  inverse_is_ringHomomorphism : RingHomomorphism inverse

instance {R S : Type*} [Ring R] [Ring S] :
    CoeFun (RingIsomorphism R S) (fun _ ↦ R → S) :=
  ⟨RingIsomorphism.toFun⟩

/-- 把旧教材兼容载体无损转换为正式环同构 `RingEquiv`。新证明应优先以
`RingEquiv` 为所有者；本转换只服务旧接口兼容。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def RingIsomorphism.toRingEquiv
    {R S : Type*} [Ring R] [Ring S] (e : RingIsomorphism R S) : R ≃+* S :=
  RingEquiv.mk
    { toFun := e.toFun
      invFun := e.inverse
      left_inv := e.left_inverse
      right_inv := e.right_inverse }
    e.toFun_is_ringHomomorphism.2.2.2.1
    e.toFun_is_ringHomomorphism.2.2.1

/-- 把正式 `RingEquiv` 无损退回旧教材兼容载体。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def RingIsomorphism.ofRingEquiv
    {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) : RingIsomorphism R S :=
  { toFun := e
    inverse := e.symm
    left_inverse := e.symm_apply_apply
    right_inverse := e.apply_symm_apply
    toFun_is_ringHomomorphism :=
      ⟨e.map_zero, e.map_one, e.map_add, e.map_mul, e.map_neg⟩
    inverse_is_ringHomomorphism :=
      ⟨e.symm.map_zero, e.symm.map_one, e.symm.map_add,
        e.symm.map_mul, e.symm.map_neg⟩ }

/-- 正式环同构经旧兼容载体往返后保持不变。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem RingIsomorphism.toRingEquiv_ofRingEquiv
    {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    (RingIsomorphism.ofRingEquiv e).toRingEquiv = e := by
  apply RingEquiv.ext
  intro x
  rfl

/-- 旧兼容载体经正式环同构往返后保持不变。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem RingIsomorphism.ofRingEquiv_toRingEquiv
    {R S : Type*} [Ring R] [Ring S] (e : RingIsomorphism R S) :
    RingIsomorphism.ofRingEquiv e.toRingEquiv = e := by
  cases e
  rfl

/-- **双边理想的教材承载**：一个环元素集合及其双边理想封闭性证明。

名称刻意避开 Mathlib 的理想结构名称；公开定理可量化该承载而不泄漏实现后端。
> **Entry**: abstract-algebra.ring.iso-theorems-/
structure TwoSidedIdealCarrier (R : Type*) [Ring R] where
  carrier : Set R
  isTwoSided : TwoSidedIdealSet carrier

instance {R : Type*} [Ring R] : SetLike (TwoSidedIdealCarrier R) R where
  coe := TwoSidedIdealCarrier.carrier
  coe_injective := by intro I J h; cases I; cases J; simp_all

/-- 旧双边理想载体无损转换为正式 `TwoSidedIdeal`。-/
def TwoSidedIdealCarrier.toTwoSidedIdeal {R : Type*} [Ring R]
    (I : TwoSidedIdealCarrier R) : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' I.carrier I.isTwoSided.1.1
    (fun {_ _} hx hy => I.isTwoSided.1.2.1 hx hy)
    (fun {_} hx => I.isTwoSided.1.2.2.1 hx)
    (fun {_ _} hx => I.isTwoSided.1.2.2.2 _ hx)
    (fun {_ _} hx => I.isTwoSided.2.2.2.2 _ hx)

/-- 正式 `TwoSidedIdeal` 无损退回旧兼容载体。-/
def TwoSidedIdealCarrier.ofTwoSidedIdeal {R : Type*} [Ring R]
    (I : TwoSidedIdeal R) : TwoSidedIdealCarrier R :=
  { carrier := I
    isTwoSided :=
      ⟨⟨I.zero_mem, (fun _ _ => I.add_mem), (fun _ => I.neg_mem),
          (fun _ _ h => I.mul_mem_left _ _ h)⟩,
        ⟨I.zero_mem, (fun _ _ => I.add_mem), (fun _ => I.neg_mem),
          (fun _ _ h => I.mul_mem_right _ _ h)⟩⟩ }

@[simp] theorem TwoSidedIdealCarrier.coe_toTwoSidedIdeal
    {R : Type*} [Ring R] (I : TwoSidedIdealCarrier R) :
    (I.toTwoSidedIdeal : Set R) = I.carrier := by
  unfold TwoSidedIdealCarrier.toTwoSidedIdeal
  apply TwoSidedIdeal.coe_mk'

@[simp] theorem TwoSidedIdealCarrier.toTwoSidedIdeal_ofTwoSidedIdeal
    {R : Type*} [Ring R] (I : TwoSidedIdeal R) :
    (TwoSidedIdealCarrier.ofTwoSidedIdeal I).toTwoSidedIdeal = I := by
  apply TwoSidedIdeal.ext
  intro x
  simp [TwoSidedIdealCarrier.toTwoSidedIdeal,
    TwoSidedIdealCarrier.ofTwoSidedIdeal, TwoSidedIdeal.mem_mk']

@[simp] theorem TwoSidedIdealCarrier.ofTwoSidedIdeal_toTwoSidedIdeal
    {R : Type*} [Ring R] (I : TwoSidedIdealCarrier R) :
    TwoSidedIdealCarrier.ofTwoSidedIdeal I.toTwoSidedIdeal = I := by
  apply SetLike.coe_injective
  ext x
  simp [TwoSidedIdealCarrier.toTwoSidedIdeal,
    TwoSidedIdealCarrier.ofTwoSidedIdeal]

/-- 把普通函数上的教材 `RingHomomorphism` 谓词打包为正式 `RingHom`。-/
def ringHomOfRingHomomorphism {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : R →+* S where
  toFun := f
  map_one' := hf.2.1
  map_mul' := hf.2.2.2.1
  map_zero' := hf.1
  map_add' := hf.2.2.1

set_option warn.classDefReducibility false in
/-- 从已证明的 `quotientRingSet_ringAxioms` 打包本库商集的标准 `Ring` 实例。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[reducible] def quotientRingSetRing {R : Type*} [Ring R] (I : Set R)
    (hI : TwoSidedIdealSet I) : Ring (quotientRingSet I hI) := by
  let A := quotientRingSet_ringAxioms I hI
  exact Ring.ofMinimalAxioms A.add_assoc A.zero_add A.add_left_neg
    A.mul_assoc A.one_mul A.mul_one A.left_distrib A.right_distrib

attribute [local instance] quotientRingSetRing

/-- 普通函数形式环同态的核集合。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def ringHomKernelSet {R S : Type*} [Ring R] [Ring S] (f : R → S) : Set R :=
  {x | f x = 0}

/-- 环同态核对加法、取负和双侧乘法封闭，因而是双边理想。
> **Entry**: abstract-algebra.ring.iso-theorems-/
theorem ringHomKernelSet_isTwoSidedIdeal {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) :
    TwoSidedIdealSet (ringHomKernelSet f) := by
  have hzero : (0 : R) ∈ ringHomKernelSet f := hf.1
  have hadd : ∀ ⦃x y : R⦄, x ∈ ringHomKernelSet f → y ∈ ringHomKernelSet f →
      x + y ∈ ringHomKernelSet f := by
    intro x y hx hy
    change f (x + y) = 0
    rw [hf.2.2.1, hx, hy, add_zero]
  have hneg : ∀ ⦃x : R⦄, x ∈ ringHomKernelSet f → -x ∈ ringHomKernelSet f := by
    intro x hx
    change f (-x) = 0
    rw [hf.2.2.2.2, hx, neg_zero]
  exact ⟨⟨hzero, hadd, hneg, by
    intro r x hx
    change f (r * x) = 0
    rw [hf.2.2.2.1, hx, mul_zero]⟩,
    ⟨hzero, hadd, hneg, by
      intro r x hx
      change f (x * r) = 0
      rw [hf.2.2.2.1, hx, zero_mul]⟩⟩

/-- 将环同态核集合与其双边理想证明打包。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def ringHomKernel {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : TwoSidedIdealCarrier R :=
  TwoSidedIdealCarrier.ofTwoSidedIdeal
    (TwoSidedIdeal.ker (ringHomOfRingHomomorphism f hf))

/-- 旧核载体转换后正是正式 `TwoSidedIdeal.ker`。-/
@[simp] theorem ringHomKernel_toTwoSidedIdeal {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) :
    (ringHomKernel f hf).toTwoSidedIdeal =
      TwoSidedIdeal.ker (ringHomOfRingHomomorphism f hf) := by
  apply TwoSidedIdealCarrier.toTwoSidedIdeal_ofTwoSidedIdeal

/-- **环同态的像**：由“存在原像”刻画的教材子类型。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def ringHomRange {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (_hf : RingHomomorphism f) :=
  {y : S // ∃ x : R, f x = y}

instance ringHomRangeZero {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : Zero (ringHomRange f hf) :=
  ⟨⟨0, 0, hf.1⟩⟩

instance ringHomRangeOne {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : One (ringHomRange f hf) :=
  ⟨⟨1, 1, hf.2.1⟩⟩

instance ringHomRangeAdd {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : Add (ringHomRange f hf) :=
  ⟨fun a b ↦ ⟨a.1 + b.1, by
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    exact ⟨x + y, (hf.2.2.1 x y).trans (congrArg₂ (· + ·) hx hy)⟩⟩⟩

instance ringHomRangeMul {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : Mul (ringHomRange f hf) :=
  ⟨fun a b ↦ ⟨a.1 * b.1, by
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    exact ⟨x * y, (hf.2.2.2.1 x y).trans (congrArg₂ (· * ·) hx hy)⟩⟩⟩

instance ringHomRangeNeg {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : Neg (ringHomRange f hf) :=
  ⟨fun a ↦ ⟨-a.1, by
    obtain ⟨x, hx⟩ := a.2
    exact ⟨-x, (hf.2.2.2.2 x).trans (congrArg Neg.neg hx)⟩⟩⟩

set_option warn.classDefReducibility false in
/-- 环同态的像在逐点运算下构成环。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[reducible] def ringHomRangeRing {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : Ring (ringHomRange f hf) := by
  apply Ring.ofMinimalAxioms
  · intro a b c; apply Subtype.ext; exact add_assoc _ _ _
  · intro a; apply Subtype.ext; exact zero_add _
  · intro a; apply Subtype.ext; exact neg_add_cancel _
  · intro a b c; apply Subtype.ext; exact mul_assoc _ _ _
  · intro a; apply Subtype.ext; exact one_mul _
  · intro a; apply Subtype.ext; exact mul_one _
  · intro a b c; apply Subtype.ext; exact mul_add _ _ _
  · intro a b c; apply Subtype.ext; exact add_mul _ _ _

attribute [local instance] ringHomRangeRing

/-- 将原环元素送到其像中对应元素的满射。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def ringHomRangeMap {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) : R → ringHomRange f hf :=
  fun x ↦ ⟨f x, x, rfl⟩

/-- 到教材像承载的规范映射是本库意义下的环同态。
> **Entry**: abstract-algebra.ring.iso-theorems-/
theorem ringHomRangeMap_is_ringHomomorphism {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) :
    RingHomomorphism (ringHomRangeMap f hf) := by
  refine ⟨Subtype.ext hf.1, Subtype.ext hf.2.1, ?_, ?_, ?_⟩
  · intro x y; exact Subtype.ext (hf.2.2.1 x y)
  · intro x y; exact Subtype.ext (hf.2.2.2.1 x y)
  · intro x; exact Subtype.ext (hf.2.2.2.2 x)

/-- **环的第一同构定理（正式承载）**：本库显式商环 `R / ker(f)` 与教材像承载同构。

逆函数从像元素选择一个原像；不同选择相差一个核元素，故给出相同商类。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def ringFirstEquiv {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) :
    RingEquiv
      (quotientRingSet (ringHomKernelSet f) (ringHomKernelSet_isTwoSidedIdeal f hf))
      (ringHomRange f hf) := by
  classical
  let K : Set R := ringHomKernelSet f
  let hK : TwoSidedIdealSet K := ringHomKernelSet_isTwoSidedIdeal f hf
  let g : R → ringHomRange f hf := ringHomRangeMap f hf
  let hg : RingHomomorphism g := ringHomRangeMap_is_ringHomomorphism f hf
  have hker : ∀ x : R, x ∈ K → g x = 0 := by
    intro x hx
    apply Subtype.ext
    exact hx
  let forward : quotientRingSet K hK → ringHomRange f hf :=
    quotientRingSetLift K hK g hg hker
  let representative : ringHomRange f hf → R := fun y ↦ y.2.choose
  have representative_spec (y : ringHomRange f hf) : f (representative y) = y.1 :=
    y.2.choose_spec
  let inverse : ringHomRange f hf → quotientRingSet K hK :=
    fun y ↦ quotientRingProjection K hK (representative y)
  have hleft : ∀ q : quotientRingSet K hK, inverse (forward q) = q := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    apply (quotientRingProjection_eq_iff hK (representative (g x)) x).2
    change f (representative (g x) - x) = 0
    calc
      f (representative (g x) - x) =
          f (representative (g x)) - f x := by
            rw [sub_eq_add_neg, hf.2.2.1, hf.2.2.2.2, sub_eq_add_neg]
      _ = 0 := sub_eq_zero.mpr (representative_spec (g x))
  have hright : ∀ y : ringHomRange f hf, forward (inverse y) = y := by
    intro y
    apply Subtype.ext
    exact representative_spec y
  have hforward : RingHomomorphism forward :=
    quotientRingSetLift_is_ringHomomorphism K hK g hg hker
  exact RingEquiv.mk
    { toFun := forward
      invFun := inverse
      left_inv := hleft
      right_inv := hright }
    hforward.2.2.2.1 hforward.2.2.1

/-- 第一同构定理的旧载体兼容接口；证明由 `ringFirstEquiv` 拥有。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def ringFirstIsomorphism {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) :
    RingIsomorphism
      (quotientRingSet (ringHomKernelSet f) (ringHomKernelSet_isTwoSidedIdeal f hf))
      (ringHomRange f hf) :=
  RingIsomorphism.ofRingEquiv (ringFirstEquiv f hf)

/-- 正式第一同构在投影代表元上的显式公式：`[x]` 被送到像中的 `f(x)`。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem ringFirstEquiv_projection {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (x : R) :
    ringFirstEquiv f hf
      (quotientRingProjection (ringHomKernelSet f)
        (ringHomKernelSet_isTwoSidedIdeal f hf) x) =
      ringHomRangeMap f hf x := by
  unfold ringFirstEquiv
  dsimp only
  rfl

/-- 旧第一同构兼容接口的代表元公式。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem ringFirstIsomorphism_projection {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (x : R) :
    ringFirstIsomorphism f hf
      (quotientRingProjection (ringHomKernelSet f)
        (ringHomKernelSet_isTwoSidedIdeal f hf) x) =
      ringHomRangeMap f hf x := by
  exact ringFirstEquiv_projection f hf x

/-! ### 第二阶段：理想的映射、逆映射与商环对应 -/

/-- 双边理想的显式包含关系：`I ≤ J` 表示 `I` 的每个元素都属于 `J`。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def twoSidedIdealContained {R : Type*} [Ring R]
    (I J : TwoSidedIdealCarrier R) : Prop := (I : Set R) ⊆ J

instance {R : Type*} [Ring R] : LE (TwoSidedIdealCarrier R) :=
  ⟨twoSidedIdealContained⟩

instance {R : Type*} [Ring R] : PartialOrder (TwoSidedIdealCarrier R) := by
  refine { le_refl := ?_, le_trans := ?_, le_antisymm := ?_ }
  · intro I x hx; exact hx
  · intro I J K hIJ hJK x hx; exact hJK (hIJ hx)
  · intro I J hIJ hJI
    apply SetLike.coe_injective
    exact Set.Subset.antisymm hIJ hJI

/-- 旧、正式双边理想载体之间的保序等价。-/
def TwoSidedIdealCarrier.orderIso {R : Type*} [Ring R] :
    TwoSidedIdealCarrier R ≃o TwoSidedIdeal R where
  toFun := TwoSidedIdealCarrier.toTwoSidedIdeal
  invFun := TwoSidedIdealCarrier.ofTwoSidedIdeal
  left_inv := TwoSidedIdealCarrier.ofTwoSidedIdeal_toTwoSidedIdeal
  right_inv := TwoSidedIdealCarrier.toTwoSidedIdeal_ofTwoSidedIdeal
  map_rel_iff' := by
    intro I J
    simp only [TwoSidedIdeal.le_iff]
    change (I.toTwoSidedIdeal : Set R) ⊆ (J.toTwoSidedIdeal : Set R) ↔
      (I : Set R) ⊆ J
    rw [I.coe_toTwoSidedIdeal, J.coe_toTwoSidedIdeal]
    rfl

/-- 环同态下理想的逆像；不要求同态满射。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def idealComap {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (J : TwoSidedIdealCarrier S) :
    TwoSidedIdealCarrier R :=
  TwoSidedIdealCarrier.ofTwoSidedIdeal
    (TwoSidedIdeal.comap (ringHomOfRingHomomorphism f hf) J.toTwoSidedIdeal)

@[simp] theorem idealComap_toTwoSidedIdeal {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (J : TwoSidedIdealCarrier S) :
    (idealComap f hf J).toTwoSidedIdeal =
      TwoSidedIdeal.comap (ringHomOfRingHomomorphism f hf) J.toTwoSidedIdeal := by
  apply TwoSidedIdealCarrier.toTwoSidedIdeal_ofTwoSidedIdeal

/-- 元素属于理想逆像，当且仅当其函数值属于目标理想。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem mem_idealComap_iff {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (J : TwoSidedIdealCarrier S) (x : R) :
    x ∈ idealComap f hf J ↔ f x ∈ J := by
  change x ∈ (TwoSidedIdeal.comap (ringHomOfRingHomomorphism f hf)
    J.toTwoSidedIdeal) ↔ f x ∈ J
  rw [TwoSidedIdeal.mem_comap]
  change f x ∈ (J.toTwoSidedIdeal : Set S) ↔ f x ∈ (J : Set S)
  rw [J.coe_toTwoSidedIdeal]
  rfl

/-- 满射环同态下理想的像；满射性用于把目标环乘子提升回源环。
> **Entry**: abstract-algebra.ring.iso-theorems-/
private def idealMapDirectOfSurjective {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (hsurj : Function.Surjective f)
    (I : TwoSidedIdealCarrier R) : TwoSidedIdealCarrier S := by
  refine ⟨{y | ∃ x : R, x ∈ I ∧ f x = y}, ?_⟩
  constructor
  · refine ⟨⟨0, I.isTwoSided.1.1, hf.1⟩, ?_, ?_, ?_⟩
    · rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, I.isTwoSided.1.2.1 hx hy, hf.2.2.1 x y⟩
    · rintro a ⟨x, hx, rfl⟩
      exact ⟨-x, I.isTwoSided.1.2.2.1 hx, hf.2.2.2.2 x⟩
    · rintro s a ⟨x, hx, rfl⟩
      obtain ⟨r, rfl⟩ := hsurj s
      exact ⟨r * x, I.isTwoSided.1.2.2.2 r hx, hf.2.2.2.1 r x⟩
  · refine ⟨⟨0, I.isTwoSided.2.1, hf.1⟩, ?_, ?_, ?_⟩
    · rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, I.isTwoSided.2.2.1 hx hy, hf.2.2.1 x y⟩
    · rintro a ⟨x, hx, rfl⟩
      exact ⟨-x, I.isTwoSided.2.2.2.1 hx, hf.2.2.2.2 x⟩
    · rintro s a ⟨x, hx, rfl⟩
      obtain ⟨r, rfl⟩ := hsurj s
      exact ⟨x * r, I.isTwoSided.2.2.2.2 r hx, hf.2.2.2.1 x r⟩

private theorem idealMapDirect_toTwoSidedIdeal
    {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (hsurj : Function.Surjective f)
    (I : TwoSidedIdealCarrier R) :
    (idealMapDirectOfSurjective f hf hsurj I).toTwoSidedIdeal =
      TwoSidedIdeal.map (ringHomOfRingHomomorphism f hf) I.toTwoSidedIdeal := by
  apply le_antisymm
  · intro y hy
    have hyCarrier : y ∈ (idealMapDirectOfSurjective f hf hsurj I).carrier := by
      change y ∈ ((idealMapDirectOfSurjective f hf hsurj I).toTwoSidedIdeal : Set S) at hy
      rw [TwoSidedIdealCarrier.coe_toTwoSidedIdeal] at hy
      exact hy
    obtain ⟨x, hx, rfl⟩ := hyCarrier
    apply TwoSidedIdeal.subset_span
    exact ⟨x, by
      rw [I.coe_toTwoSidedIdeal]
      exact hx, rfl⟩
  · apply (TwoSidedIdeal.span_le).2
    rintro y ⟨x, hx, rfl⟩
    have hxCarrier : x ∈ I.carrier := by
      change x ∈ (I.toTwoSidedIdeal : Set R) at hx
      rw [I.coe_toTwoSidedIdeal] at hx
      exact hx
    change f x ∈ ((idealMapDirectOfSurjective f hf hsurj I).toTwoSidedIdeal : Set S)
    rw [TwoSidedIdealCarrier.coe_toTwoSidedIdeal]
    exact ⟨x, hxCarrier, rfl⟩

/-- 满射环同态下理想的像；正式所有权落在 `TwoSidedIdeal.map`。-/
def idealMapOfSurjective {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (_hsurj : Function.Surjective f)
    (I : TwoSidedIdealCarrier R) : TwoSidedIdealCarrier S :=
  TwoSidedIdealCarrier.ofTwoSidedIdeal
    (TwoSidedIdeal.map (ringHomOfRingHomomorphism f hf) I.toTwoSidedIdeal)

@[simp] theorem idealMapOfSurjective_toTwoSidedIdeal
    {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (hsurj : Function.Surjective f)
    (I : TwoSidedIdealCarrier R) :
    (idealMapOfSurjective f hf hsurj I).toTwoSidedIdeal =
      TwoSidedIdeal.map (ringHomOfRingHomomorphism f hf) I.toTwoSidedIdeal := by
  apply TwoSidedIdealCarrier.toTwoSidedIdeal_ofTwoSidedIdeal

/-- 元素属于满射理想像的存在原像刻画。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem mem_idealMapOfSurjective_iff {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (hsurj : Function.Surjective f)
    (I : TwoSidedIdealCarrier R) (y : S) :
    y ∈ idealMapOfSurjective f hf hsurj I ↔ ∃ x : R, x ∈ I ∧ f x = y := by
  change y ∈ TwoSidedIdeal.map (ringHomOfRingHomomorphism f hf)
    I.toTwoSidedIdeal ↔ ∃ x : R, x ∈ I ∧ f x = y
  rw [← idealMapDirect_toTwoSidedIdeal f hf hsurj I]
  change y ∈ ((idealMapDirectOfSurjective f hf hsurj I).toTwoSidedIdeal : Set S) ↔ _
  rw [TwoSidedIdealCarrier.coe_toTwoSidedIdeal]
  rfl

/-- 理想逆像保持包含关系。
> **Entry**: abstract-algebra.ring.iso-theorems-/
theorem idealComap_mono {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) :
    Monotone (idealComap f hf) := by
  intro I J hIJ x hx
  exact hIJ hx

/-- 满射理想像保持包含关系。
> **Entry**: abstract-algebra.ring.iso-theorems-/
theorem idealMapOfSurjective_mono {R S : Type*} [Ring R] [Ring S]
    (f : R → S) (hf : RingHomomorphism f) (hsurj : Function.Surjective f) :
    Monotone (idealMapOfSurjective f hf hsurj) := by
  intro I J hIJ y hy
  obtain ⟨x, hx, rfl⟩ :=
    (mem_idealMapOfSurjective_iff f hf hsurj I y).1 hy
  exact (mem_idealMapOfSurjective_iff f hf hsurj J (f x)).2
    ⟨x, hIJ hx, rfl⟩

/-- 本库商投影是满射：每个商类都有代表元。
> **Entry**: abstract-algebra.ring.iso-theorems-/
theorem quotientRingProjection_surjective {R : Type*} [Ring R]
    (I : Set R) (hI : TwoSidedIdealSet I) :
    Function.Surjective (quotientRingProjection I hI) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨x, rfl⟩

/-- 若 `K ≤ I`，先沿 `R → R/K` 取理想像再取逆像，逐元素恰好回到 `I`。
> **Entry**: abstract-algebra.ring.iso-theorems-/
theorem quotientIdealComapMap_membership {R : Type*} [Ring R]
    (K I : TwoSidedIdealCarrier R) (hKI : K ≤ I) (x : R) :
    x ∈ idealComap (quotientRingProjection K.carrier K.isTwoSided)
      (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)
      (idealMapOfSurjective (quotientRingProjection K.carrier K.isTwoSided)
        (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)
        (quotientRingProjection_surjective K.carrier K.isTwoSided) I) ↔ x ∈ I := by
  rw [mem_idealComap_iff, mem_idealMapOfSurjective_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hdiff : y - x ∈ K :=
      (quotientRingProjection_eq_iff K.isTwoSided y x).1 hyx
    have hneg : -(y - x) ∈ I := I.isTwoSided.1.2.2.1 (hKI hdiff)
    have hadd : -(y - x) + y ∈ I := I.isTwoSided.1.2.1 hneg hy
    convert hadd using 1
    noncomm_ring
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- 商环理想先取逆像再沿商投影取像，逐元素恰好回到原理想。
> **Entry**: abstract-algebra.ring.iso-theorems-/
theorem quotientIdealMapComap_membership {R : Type*} [Ring R]
    (K : TwoSidedIdealCarrier R)
    (J : TwoSidedIdealCarrier (quotientRingSet K.carrier K.isTwoSided))
    (q : quotientRingSet K.carrier K.isTwoSided) :
    q ∈ idealMapOfSurjective (quotientRingProjection K.carrier K.isTwoSided)
      (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)
      (quotientRingProjection_surjective K.carrier K.isTwoSided)
      (idealComap (quotientRingProjection K.carrier K.isTwoSided)
        (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided) J) ↔ q ∈ J := by
  rw [mem_idealMapOfSurjective_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_idealComap_iff _ _ _ _).mp hx
  · intro hq
    obtain ⟨x, rfl⟩ := quotientRingProjection_surjective K.carrier K.isTwoSided q
    exact ⟨x, (mem_idealComap_iff _ _ _ _).2 hq, rfl⟩

/-- **商环理想对应的保序等价数据**：包含 `K` 的原环双边理想与 `R/K` 的双边理想
之间有互逆且双向保序的映射。
> **Entry**: abstract-algebra.ring.iso-theorems-/
structure QuotientIdealOrderEquivalence (R : Type*) [Ring R]
    (K : TwoSidedIdealCarrier R) where
  toFun : {I : TwoSidedIdealCarrier R // K ≤ I} →
    TwoSidedIdealCarrier (quotientRingSet K.carrier K.isTwoSided)
  inverse : TwoSidedIdealCarrier (quotientRingSet K.carrier K.isTwoSided) →
    {I : TwoSidedIdealCarrier R // K ≤ I}
  left_inverse : ∀ I, inverse (toFun I) = I
  right_inverse : ∀ J, toFun (inverse J) = J
  monotone_toFun : Monotone toFun
  monotone_inverse : Monotone inverse

private theorem quotientTwoSidedIdeal_comap_map_membership
    {R : Type*} [Ring R] (K : TwoSidedIdealCarrier R)
    (I : TwoSidedIdeal R) (hKI : K.toTwoSidedIdeal ≤ I) (x : R) :
    x ∈ TwoSidedIdeal.comap
        (ringHomOfRingHomomorphism
          (quotientRingProjection K.carrier K.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided))
        (TwoSidedIdeal.map
          (ringHomOfRingHomomorphism
            (quotientRingProjection K.carrier K.isTwoSided)
            (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)) I) ↔
      x ∈ I := by
  let Iold := TwoSidedIdealCarrier.ofTwoSidedIdeal I
  have hKIold : K ≤ Iold := by
    intro y hy
    apply hKI
    change y ∈ (K.toTwoSidedIdeal : Set R)
    rw [K.coe_toTwoSidedIdeal]
    exact hy
  have hIold : Iold.toTwoSidedIdeal = I :=
    TwoSidedIdealCarrier.toTwoSidedIdeal_ofTwoSidedIdeal I
  rw [← hIold]
  rw [← idealMapOfSurjective_toTwoSidedIdeal
    (quotientRingProjection K.carrier K.isTwoSided)
    (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)
    (quotientRingProjection_surjective K.carrier K.isTwoSided) Iold]
  rw [← idealComap_toTwoSidedIdeal
    (quotientRingProjection K.carrier K.isTwoSided)
    (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)]
  change x ∈ ((idealComap
      (quotientRingProjection K.carrier K.isTwoSided)
      (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)
      (idealMapOfSurjective
        (quotientRingProjection K.carrier K.isTwoSided)
        (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)
        (quotientRingProjection_surjective K.carrier K.isTwoSided) Iold)).toTwoSidedIdeal : Set R) ↔
    x ∈ (Iold.toTwoSidedIdeal : Set R)
  rw [TwoSidedIdealCarrier.coe_toTwoSidedIdeal,
    TwoSidedIdealCarrier.coe_toTwoSidedIdeal]
  exact quotientIdealComapMap_membership K Iold hKIold x

private theorem quotientTwoSidedIdeal_map_comap_membership
    {R : Type*} [Ring R] (K : TwoSidedIdealCarrier R)
    (J : TwoSidedIdeal (quotientRingSet K.carrier K.isTwoSided))
    (q : quotientRingSet K.carrier K.isTwoSided) :
    q ∈ TwoSidedIdeal.map
        (ringHomOfRingHomomorphism
          (quotientRingProjection K.carrier K.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided))
        (TwoSidedIdeal.comap
          (ringHomOfRingHomomorphism
            (quotientRingProjection K.carrier K.isTwoSided)
            (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)) J) ↔
      q ∈ J := by
  let Jold := TwoSidedIdealCarrier.ofTwoSidedIdeal J
  have hJold : Jold.toTwoSidedIdeal = J :=
    TwoSidedIdealCarrier.toTwoSidedIdeal_ofTwoSidedIdeal J
  rw [← hJold]
  rw [← idealComap_toTwoSidedIdeal
    (quotientRingProjection K.carrier K.isTwoSided)
    (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided) Jold]
  rw [← idealMapOfSurjective_toTwoSidedIdeal
    (quotientRingProjection K.carrier K.isTwoSided)
    (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)
    (quotientRingProjection_surjective K.carrier K.isTwoSided)]
  change q ∈ ((idealMapOfSurjective
      (quotientRingProjection K.carrier K.isTwoSided)
      (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided)
      (quotientRingProjection_surjective K.carrier K.isTwoSided)
      (idealComap
        (quotientRingProjection K.carrier K.isTwoSided)
        (quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided) Jold)).toTwoSidedIdeal :
      Set (quotientRingSet K.carrier K.isTwoSided)) ↔
    q ∈ (Jold.toTwoSidedIdeal : Set (quotientRingSet K.carrier K.isTwoSided))
  rw [TwoSidedIdealCarrier.coe_toTwoSidedIdeal,
    TwoSidedIdealCarrier.coe_toTwoSidedIdeal]
  exact quotientIdealMapComap_membership K Jold q

/-- 商投影下正式双边理想的对应定理：包含 `K` 的 `TwoSidedIdeal R` 与
商环的 `TwoSidedIdeal` 保序同构。定义的正、逆方向分别就是
`TwoSidedIdeal.map` 与 `TwoSidedIdeal.comap`。-/
def quotientIdealOrderIso {R : Type*} [Ring R]
    (K : TwoSidedIdealCarrier R) :
    {I : TwoSidedIdeal R // K.toTwoSidedIdeal ≤ I} ≃o
      TwoSidedIdeal (quotientRingSet K.carrier K.isTwoSided) := by
  let projection := quotientRingProjection K.carrier K.isTwoSided
  let hprojection := quotientRingProjection_is_ringHomomorphism K.carrier K.isTwoSided
  let projectionHom := ringHomOfRingHomomorphism projection hprojection
  let hsurj := quotientRingProjection_surjective K.carrier K.isTwoSided
  let forward : {I : TwoSidedIdeal R // K.toTwoSidedIdeal ≤ I} →
      TwoSidedIdeal (quotientRingSet K.carrier K.isTwoSided) :=
    fun I ↦ TwoSidedIdeal.map projectionHom I.1
  let backward : TwoSidedIdeal (quotientRingSet K.carrier K.isTwoSided) →
      {I : TwoSidedIdeal R // K.toTwoSidedIdeal ≤ I} := fun J ↦
    ⟨TwoSidedIdeal.comap projectionHom J, by
      intro x hx
      have hzero : projection x = 0 := by
        change x ∈ {z : R | quotientRingProjection K.carrier K.isTwoSided z = 0}
        rw [quotientRingProjection_kernel K.carrier K.isTwoSided]
        change x ∈ (K.toTwoSidedIdeal : Set R) at hx
        rw [K.coe_toTwoSidedIdeal] at hx
        exact hx
      change projection x ∈ J
      rw [hzero]
      exact J.zero_mem⟩
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · intro I
    apply Subtype.ext
    apply TwoSidedIdeal.ext
    intro x
    exact quotientTwoSidedIdeal_comap_map_membership K I.1 I.2 x
  · intro J
    apply TwoSidedIdeal.ext
    intro q
    exact quotientTwoSidedIdeal_map_comap_membership K J q
  · intro I J
    constructor
    · intro h x hx
      apply (quotientTwoSidedIdeal_comap_map_membership K J.1 J.2 x).1
      apply (TwoSidedIdeal.mem_comap projectionHom).2
      apply h
      exact (TwoSidedIdeal.mem_comap projectionHom).1
        ((quotientTwoSidedIdeal_comap_map_membership K I.1 I.2 x).2 hx)
    · intro h
      exact TwoSidedIdeal.map_mono projectionHom h

/-- 旧商理想对应数据无损转为标准 `OrderIso`。-/
def QuotientIdealOrderEquivalence.toOrderIso
    {R : Type*} [Ring R] {K : TwoSidedIdealCarrier R}
    (e : QuotientIdealOrderEquivalence R K) :
    {I : TwoSidedIdealCarrier R // K ≤ I} ≃o
      TwoSidedIdealCarrier (quotientRingSet K.carrier K.isTwoSided) := by
  exact
    { toEquiv :=
        { toFun := e.toFun
          invFun := e.inverse
          left_inv := e.left_inverse
          right_inv := e.right_inverse }
      map_rel_iff' := by
        intro I J
        constructor
        · intro h
          change e.toFun I ≤ e.toFun J at h
          have hh := e.monotone_inverse h
          rw [e.left_inverse I, e.left_inverse J] at hh
          exact hh
        · intro h
          change e.toFun I ≤ e.toFun J
          exact e.monotone_toFun h }

/-- 标准 `OrderIso` 无损退回旧商理想对应数据。-/
def QuotientIdealOrderEquivalence.ofOrderIso
    {R : Type*} [Ring R] {K : TwoSidedIdealCarrier R}
    (e : {I : TwoSidedIdealCarrier R // K ≤ I} ≃o
      TwoSidedIdealCarrier (quotientRingSet K.carrier K.isTwoSided)) :
    QuotientIdealOrderEquivalence R K where
  toFun := e
  inverse := e.symm
  left_inverse := e.symm_apply_apply
  right_inverse := e.apply_symm_apply
  monotone_toFun := e.monotone
  monotone_inverse := e.symm.monotone

@[simp] theorem QuotientIdealOrderEquivalence.toOrderIso_ofOrderIso
    {R : Type*} [Ring R] {K : TwoSidedIdealCarrier R}
    (e : {I : TwoSidedIdealCarrier R // K ≤ I} ≃o
      TwoSidedIdealCarrier (quotientRingSet K.carrier K.isTwoSided)) :
    (QuotientIdealOrderEquivalence.ofOrderIso e).toOrderIso = e := by
  apply OrderIso.ext
  rfl

@[simp] theorem QuotientIdealOrderEquivalence.ofOrderIso_toOrderIso
    {R : Type*} [Ring R] {K : TwoSidedIdealCarrier R}
    (e : QuotientIdealOrderEquivalence R K) :
    QuotientIdealOrderEquivalence.ofOrderIso e.toOrderIso = e := by
  cases e
  rfl

private def quotientIdealCarrierSubtypeOrderIso {R : Type*} [Ring R]
    (K : TwoSidedIdealCarrier R) :
    {I : TwoSidedIdealCarrier R // K ≤ I} ≃o
      {I : TwoSidedIdeal R // K.toTwoSidedIdeal ≤ I} where
  toFun := fun I ↦ ⟨I.1.toTwoSidedIdeal, by
    intro x hx
    have hxCarrier : x ∈ K := by
      change x ∈ (K.toTwoSidedIdeal : Set R) at hx
      rw [K.coe_toTwoSidedIdeal] at hx
      exact hx
    change x ∈ (I.1.toTwoSidedIdeal : Set R)
    rw [I.1.coe_toTwoSidedIdeal]
    exact I.2 hxCarrier⟩
  invFun := fun I ↦ ⟨TwoSidedIdealCarrier.ofTwoSidedIdeal I.1, by
    intro x hx
    apply I.2
    change x ∈ (K.toTwoSidedIdeal : Set R)
    rw [K.coe_toTwoSidedIdeal]
    exact hx⟩
  left_inv := by
    intro I
    apply Subtype.ext
    exact TwoSidedIdealCarrier.ofTwoSidedIdeal_toTwoSidedIdeal I.1
  right_inv := by
    intro I
    apply Subtype.ext
    exact TwoSidedIdealCarrier.toTwoSidedIdeal_ofTwoSidedIdeal I.1
  map_rel_iff' := by
    intro I J
    change I.1.toTwoSidedIdeal ≤ J.1.toTwoSidedIdeal ↔ I.1 ≤ J.1
    exact TwoSidedIdealCarrier.orderIso.le_iff_le

/-- **理想对应定理**：包含 `K` 的双边理想与商环 `R/K` 的双边理想保序对应。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def quotientIdealCorrespondence {R : Type*} [Ring R]
    (K : TwoSidedIdealCarrier R) :
    QuotientIdealOrderEquivalence R K :=
  QuotientIdealOrderEquivalence.ofOrderIso
    ((quotientIdealCarrierSubtypeOrderIso K).trans
      ((quotientIdealOrderIso K).trans TwoSidedIdealCarrier.orderIso.symm))

/-- **第三同构定理（正式承载）**：若 `I ≤ J`，则 `(R/I)/(J/I)` 与 `R/J` 环同构；这里 `J/I`
由 `J` 沿本库自然商投影的理想像显式构造。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def ringThirdEquiv {R : Type*} [Ring R]
    (I J : TwoSidedIdealCarrier R) (hIJ : I ≤ J) :
    RingEquiv
      (quotientRingSet
        (idealMapOfSurjective (quotientRingProjection I.carrier I.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided)
          (quotientRingProjection_surjective I.carrier I.isTwoSided) J).carrier
        (idealMapOfSurjective (quotientRingProjection I.carrier I.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided)
          (quotientRingProjection_surjective I.carrier I.isTwoSided) J).isTwoSided)
      (quotientRingSet J.carrier J.isTwoSided) := by
  classical
  let πI := quotientRingProjection I.carrier I.isTwoSided
  let πJ := quotientRingProjection J.carrier J.isTwoSided
  let hπI := quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided
  let hπJ := quotientRingProjection_is_ringHomomorphism J.carrier J.isTwoSided
  have hIzero : ∀ x : R, x ∈ I → πJ x = 0 := by
    intro x hx
    change quotientRingProjection J.carrier J.isTwoSided x = 0
    change x ∈ {z : R | quotientRingProjection J.carrier J.isTwoSided z = 0}
    rw [quotientRingProjection_kernel J.carrier J.isTwoSided]
    exact hIJ hx
  let g : quotientRingSet I.carrier I.isTwoSided → quotientRingSet J.carrier J.isTwoSided :=
    quotientRingSetLift I.carrier I.isTwoSided πJ hπJ hIzero
  let hg : RingHomomorphism g :=
    quotientRingSetLift_is_ringHomomorphism I.carrier I.isTwoSided πJ hπJ hIzero
  let L := idealMapOfSurjective πI hπI
    (quotientRingProjection_surjective I.carrier I.isTwoSided) J
  have hLzero : ∀ q, q ∈ L → g q = 0 := by
    intro q hq
    rw [mem_idealMapOfSurjective_iff] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    change πJ x = 0
    change x ∈ {z : R | quotientRingProjection J.carrier J.isTwoSided z = 0}
    rw [quotientRingProjection_kernel J.carrier J.isTwoSided]
    exact hx
  let forward : quotientRingSet L.carrier L.isTwoSided →
      quotientRingSet J.carrier J.isTwoSided :=
    quotientRingSetLift L.carrier L.isTwoSided g hg hLzero
  let representative : quotientRingSet J.carrier J.isTwoSided → R := fun q ↦
    (quotientRingProjection_surjective J.carrier J.isTwoSided q).choose
  have representative_spec (q : quotientRingSet J.carrier J.isTwoSided) :
      πJ (representative q) = q :=
    (quotientRingProjection_surjective J.carrier J.isTwoSided q).choose_spec
  let inverse : quotientRingSet J.carrier J.isTwoSided →
      quotientRingSet L.carrier L.isTwoSided := fun q ↦
    quotientRingProjection L.carrier L.isTwoSided (πI (representative q))
  have hleft : ∀ q, inverse (forward q) = q := by
    intro q
    refine Quotient.inductionOn q ?_
    intro qI
    refine Quotient.inductionOn qI ?_
    intro x
    apply (quotientRingProjection_eq_iff L.isTwoSided
      (πI (representative (πJ x))) (πI x)).2
    change πI (representative (πJ x)) - πI x ∈ L
    have hsub : πI (representative (πJ x) - x) =
        πI (representative (πJ x)) - πI x := by
      change quotientRingProjection I.carrier I.isTwoSided
          (representative (πJ x) - x) =
        quotientRingProjection I.carrier I.isTwoSided (representative (πJ x)) -
          quotientRingProjection I.carrier I.isTwoSided x
      rw [sub_eq_add_neg, sub_eq_add_neg]
      calc
        quotientRingProjection I.carrier I.isTwoSided (representative (πJ x) + -x) =
            quotientRingProjection I.carrier I.isTwoSided (representative (πJ x)) +
              quotientRingProjection I.carrier I.isTwoSided (-x) :=
          (quotientAdd_projection I.carrier I.isTwoSided _ _).symm
        _ = quotientRingProjection I.carrier I.isTwoSided (representative (πJ x)) +
              -quotientRingProjection I.carrier I.isTwoSided x := by
          rw [quotientNeg_projection]
    rw [← hsub]
    apply (mem_idealMapOfSurjective_iff πI hπI
      (quotientRingProjection_surjective I.carrier I.isTwoSided) J _).2
    refine ⟨representative (πJ x) - x, ?_, rfl⟩
    apply (quotientRingProjection_eq_iff J.isTwoSided
      (representative (πJ x)) x).1
    exact representative_spec (πJ x)
  have hright : ∀ q, forward (inverse q) = q := by
    intro q
    change πJ (representative q) = q
    exact representative_spec q
  have hforward : RingHomomorphism forward :=
    quotientRingSetLift_is_ringHomomorphism L.carrier L.isTwoSided g hg hLzero
  exact RingEquiv.mk
    { toFun := forward
      invFun := inverse
      left_inv := hleft
      right_inv := hright }
    hforward.2.2.2.1 hforward.2.2.1

/-- 第三同构定理的旧载体兼容接口；证明由 `ringThirdEquiv` 拥有。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def ringThirdIsomorphism {R : Type*} [Ring R]
    (I J : TwoSidedIdealCarrier R) (hIJ : I ≤ J) :
    RingIsomorphism
      (quotientRingSet
        (idealMapOfSurjective (quotientRingProjection I.carrier I.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided)
          (quotientRingProjection_surjective I.carrier I.isTwoSided) J).carrier
        (idealMapOfSurjective (quotientRingProjection I.carrier I.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided)
          (quotientRingProjection_surjective I.carrier I.isTwoSided) J).isTwoSided)
      (quotientRingSet J.carrier J.isTwoSided) :=
  RingIsomorphism.ofRingEquiv (ringThirdEquiv I J hIJ)

/-- 正式第三同构的代表元公式：二重自然投影后应用同构，等于直接模去 `J`。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem ringThirdEquiv_projection_projection
    {R : Type*} [Ring R] (I J : TwoSidedIdealCarrier R) (hIJ : I ≤ J) (x : R) :
    ringThirdEquiv I J hIJ
      (quotientRingProjection
        (idealMapOfSurjective (quotientRingProjection I.carrier I.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided)
          (quotientRingProjection_surjective I.carrier I.isTwoSided) J).carrier
        (idealMapOfSurjective (quotientRingProjection I.carrier I.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided)
          (quotientRingProjection_surjective I.carrier I.isTwoSided) J).isTwoSided
        (quotientRingProjection I.carrier I.isTwoSided x)) =
      quotientRingProjection J.carrier J.isTwoSided x := by
  unfold ringThirdEquiv
  dsimp only
  rfl

/-- 旧第三同构兼容接口的代表元公式。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem ringThirdIsomorphism_projection_projection
    {R : Type*} [Ring R] (I J : TwoSidedIdealCarrier R) (hIJ : I ≤ J) (x : R) :
    ringThirdIsomorphism I J hIJ
      (quotientRingProjection
        (idealMapOfSurjective (quotientRingProjection I.carrier I.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided)
          (quotientRingProjection_surjective I.carrier I.isTwoSided) J).carrier
        (idealMapOfSurjective (quotientRingProjection I.carrier I.isTwoSided)
          (quotientRingProjection_is_ringHomomorphism I.carrier I.isTwoSided)
          (quotientRingProjection_surjective I.carrier I.isTwoSided) J).isTwoSided
        (quotientRingProjection I.carrier I.isTwoSided x)) =
      quotientRingProjection J.carrier J.isTwoSided x := by
  exact ringThirdEquiv_projection_projection I J hIJ x

/-! ### 第三阶段：第二同构定理 -/

/-- **子环教材承载**：一个环元素集合及其 `SubringSet` 封闭性证明。
> **Entry**: abstract-algebra.ring.iso-theorems-/
structure SubringCarrier (R : Type*) [Ring R] where
  carrier : Set R
  isSubring : SubringSet carrier

instance {R : Type*} [Ring R] : SetLike (SubringCarrier R) R := by
  exact ⟨SubringCarrier.carrier, by
    intro A B h
    cases A
    cases B
    simp_all⟩

def subringCarrier {R : Type*} [Ring R] (A : Set R) (hA : SubringSet A) :
    SubringCarrier R := ⟨A, hA⟩

instance subringCarrierZero {R : Type*} [Ring R] (A : SubringCarrier R) : Zero A := by
  exact ⟨⟨0, A.isSubring.1⟩⟩
instance subringCarrierOne {R : Type*} [Ring R] (A : SubringCarrier R) : One A := by
  exact ⟨⟨1, A.isSubring.2.1⟩⟩
instance subringCarrierAdd {R : Type*} [Ring R] (A : SubringCarrier R) : Add A := by
  exact ⟨fun a b ↦ ⟨a.1 + b.1, A.isSubring.2.2.1 a.2 b.2⟩⟩
instance subringCarrierMul {R : Type*} [Ring R] (A : SubringCarrier R) : Mul A := by
  exact ⟨fun a b ↦ ⟨a.1 * b.1, A.isSubring.2.2.2.1 a.2 b.2⟩⟩
instance subringCarrierNeg {R : Type*} [Ring R] (A : SubringCarrier R) : Neg A := by
  exact ⟨fun a ↦ ⟨-a.1, A.isSubring.2.2.2.2 a.2⟩⟩

set_option warn.classDefReducibility false in
@[reducible] def subringCarrierRing {R : Type*} [Ring R]
    (A : SubringCarrier R) : Ring A := by
  apply Ring.ofMinimalAxioms
  · intro a b c; apply Subtype.ext; exact add_assoc _ _ _
  · intro a; apply Subtype.ext; exact zero_add _
  · intro a; apply Subtype.ext; exact neg_add_cancel _
  · intro a b c; apply Subtype.ext; exact mul_assoc _ _ _
  · intro a; apply Subtype.ext; exact one_mul _
  · intro a; apply Subtype.ext; exact mul_one _
  · intro a b c; apply Subtype.ext; exact mul_add _ _ _
  · intro a b c; apply Subtype.ext; exact add_mul _ _ _

attribute [local instance] subringCarrierRing

/-- `A ∩ I` 作为子环 `A` 内的双边理想。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def subringIdealIntersection {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    TwoSidedIdealCarrier A := by
  refine ⟨{a : A | a.1 ∈ I}, ?_⟩
  constructor
  · refine ⟨I.isTwoSided.1.1, ?_, ?_, ?_⟩
    · intro a b ha hb; exact I.isTwoSided.1.2.1 ha hb
    · intro a ha; exact I.isTwoSided.1.2.2.1 ha
    · intro r a ha; exact I.isTwoSided.1.2.2.2 r.1 ha
  · refine ⟨I.isTwoSided.2.1, ?_, ?_, ?_⟩
    · intro a b ha hb; exact I.isTwoSided.2.2.1 ha hb
    · intro a ha; exact I.isTwoSided.2.2.2.1 ha
    · intro r a ha; exact I.isTwoSided.2.2.2.2 r.1 ha

@[simp] theorem mem_subringIdealIntersection_iff {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) (a : A) :
    a ∈ subringIdealIntersection A I ↔ a.1 ∈ I := by
  rfl

/-- **子环与理想的和** `A + I`：所有 `a+i` 组成的子环，而不是两个理想的和。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def subringIdealSum {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) : SubringCarrier R := by
  let S : Set R := {x | ∃ a : R, a ∈ A ∧ ∃ i : R, i ∈ I ∧ a + i = x}
  refine ⟨S, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨0, A.isSubring.1, 0, I.isTwoSided.1.1, add_zero 0⟩
  · exact ⟨1, A.isSubring.2.1, 0, I.isTwoSided.1.1, add_zero 1⟩
  · rintro x y ⟨a, ha, i, hi, rfl⟩ ⟨b, hb, j, hj, rfl⟩
    exact ⟨a + b, A.isSubring.2.2.1 ha hb, i + j,
      I.isTwoSided.1.2.1 hi hj, by abel⟩
  · rintro x y ⟨a, ha, i, hi, rfl⟩ ⟨b, hb, j, hj, rfl⟩
    have haj : a * j ∈ I := I.isTwoSided.1.2.2.2 a hj
    have hib : i * b ∈ I := I.isTwoSided.2.2.2.2 b hi
    have hij : i * j ∈ I := I.isTwoSided.1.2.2.2 i hj
    exact ⟨a * b, A.isSubring.2.2.2.1 ha hb,
      a * j + i * b + i * j,
      I.isTwoSided.1.2.1 (I.isTwoSided.1.2.1 haj hib) hij, by noncomm_ring⟩
  · rintro x ⟨a, ha, i, hi, rfl⟩
    exact ⟨-a, A.isSubring.2.2.2.2 ha, -i,
      I.isTwoSided.1.2.2.1 hi, by abel⟩

@[simp] theorem mem_subringIdealSum_iff {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) (x : R) :
    x ∈ subringIdealSum A I ↔ ∃ a : R, a ∈ A ∧ ∃ i : R, i ∈ I ∧ a + i = x := by
  rfl

/-- 将 `I` 限制到和子环 `A+I`，得到右侧商 `(A+I)/I` 的双边理想。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def subringIdealInSum {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    TwoSidedIdealCarrier (subringIdealSum A I) := by
  refine ⟨{x : subringIdealSum A I | x.1 ∈ I}, ?_⟩
  constructor
  · refine ⟨I.isTwoSided.1.1, ?_, ?_, ?_⟩
    · intro x y hx hy; exact I.isTwoSided.1.2.1 hx hy
    · intro x hx; exact I.isTwoSided.1.2.2.1 hx
    · intro r x hx; exact I.isTwoSided.1.2.2.2 r.1 hx
  · refine ⟨I.isTwoSided.2.1, ?_, ?_, ?_⟩
    · intro x y hx hy; exact I.isTwoSided.2.2.1 hx hy
    · intro x hx; exact I.isTwoSided.2.2.2.1 hx
    · intro r x hx; exact I.isTwoSided.2.2.2.2 r.1 hx

/-- 子环 `A` 到和子环 `A+I` 的规范包含映射。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def subringIdealSumInclusion {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    A → subringIdealSum A I := by
  intro a
  exact ⟨a.1, a.1, a.2, 0, I.isTwoSided.1.1, add_zero a.1⟩

/-- 第二同构定理的规范映射 `A → (A+I)/I`。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def secondIsomorphismCanonicalMap {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    A → quotientRingSet (subringIdealInSum A I).carrier
      (subringIdealInSum A I).isTwoSided := by
  exact fun a ↦ quotientRingProjection (subringIdealInSum A I).carrier
    (subringIdealInSum A I).isTwoSided (subringIdealSumInclusion A I a)

theorem secondIsomorphismCanonicalMap_is_ringHomomorphism {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    RingHomomorphism (secondIsomorphismCanonicalMap A I) := by
  let L := subringIdealInSum A I
  let ι := subringIdealSumInclusion A I
  have hι : RingHomomorphism ι := by
    refine ⟨Subtype.ext rfl, Subtype.ext rfl, ?_, ?_, ?_⟩
    · intro a b; exact Subtype.ext rfl
    · intro a b; exact Subtype.ext rfl
    · intro a; exact Subtype.ext rfl
  exact ⟨by
      change quotientRingProjection L.carrier L.isTwoSided (ι 0) = 0
      rw [hι.1]
      exact (quotientZero_eq_projection L.carrier L.isTwoSided).symm,
    by
      change quotientRingProjection L.carrier L.isTwoSided (ι 1) = 1
      rw [hι.2.1]
      exact (quotientOne_eq_projection L.carrier L.isTwoSided).symm,
    fun a b ↦ by
      change quotientRingProjection L.carrier L.isTwoSided (ι (a + b)) = _
      rw [hι.2.2.1]
      exact (quotientAdd_projection L.carrier L.isTwoSided _ _).symm,
    fun a b ↦ by
      change quotientRingProjection L.carrier L.isTwoSided (ι (a * b)) = _
      rw [hι.2.2.2.1]
      exact (quotientMul_projection L.carrier L.isTwoSided _ _).symm,
    fun a ↦ by
      change quotientRingProjection L.carrier L.isTwoSided (ι (-a)) = _
      rw [hι.2.2.2.2]
      exact (quotientNeg_projection L.carrier L.isTwoSided _).symm⟩

theorem secondIsomorphismCanonicalMap_surjective {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    Function.Surjective (secondIsomorphismCanonicalMap A I) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro s
  obtain ⟨a, ha, i, hi, hai⟩ := s.2
  let aA : A := ⟨a, ha⟩
  refine ⟨aA, ?_⟩
  apply (quotientRingProjection_eq_iff (subringIdealInSum A I).isTwoSided
    (subringIdealSumInclusion A I aA) s).2
  unfold idealCongruent
  unfold subringIdealSumInclusion
  change ((⟨a, a, ha, 0, I.isTwoSided.1.1, add_zero a⟩ : subringIdealSum A I) - s).1 ∈ I
  rw [sub_eq_add_neg]
  change a + -s.1 ∈ I
  have hneg : -i ∈ I := I.isTwoSided.1.2.2.1 hi
  convert hneg using 1
  rw [← hai]
  abel

theorem secondIsomorphismCanonicalMap_kernel {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    ringHomKernelSet (secondIsomorphismCanonicalMap A I) =
      (subringIdealIntersection A I).carrier := by
  ext a
  change secondIsomorphismCanonicalMap A I a = 0 ↔ a.1 ∈ I
  unfold secondIsomorphismCanonicalMap
  rw [quotientZero_eq_projection]
  rw [quotientRingProjection_eq_iff]
  unfold idealCongruent
  change ((subringIdealSumInclusion A I a - 0 : subringIdealSum A I)).1 ∈ I ↔ _
  rw [sub_eq_add_neg]
  change (subringIdealSumInclusion A I a).1 + -(0 : subringIdealSum A I).1 ∈ I ↔ _
  change a.1 + -(0 : R) ∈ I ↔ a.1 ∈ I
  simp

/-- 本库环同构的复合。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def ringIsomorphismTrans {R S T : Type*} [Ring R] [Ring S] [Ring T]
    (e₁ : RingIsomorphism R S) (e₂ : RingIsomorphism S T) : RingIsomorphism R T :=
  RingIsomorphism.ofRingEquiv (e₁.toRingEquiv.trans e₂.toRingEquiv)

/-- 满射环同态的教材像承载与整个余域同构。
> **Entry**: abstract-algebra.ring.iso-theorems-/
private noncomputable def ringHomRangeEquivOfSurjective
    {R S : Type*} [Ring R] [Ring S] (f : R → S) (hf : RingHomomorphism f)
    (hsurj : Function.Surjective f) : RingEquiv (ringHomRange f hf) S := by
  let inverse : S → ringHomRange f hf := fun y ↦ ⟨y, hsurj y⟩
  exact RingEquiv.mk
    { toFun := fun y ↦ y.1
      invFun := inverse
      left_inv := fun y ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- 满射环同态的教材像承载与整个余域同构；旧载体接口由正式 helper 包装。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def ringHomRangeIsomorphismOfSurjective
    {R S : Type*} [Ring R] [Ring S] (f : R → S) (hf : RingHomomorphism f)
    (hsurj : Function.Surjective f) : RingIsomorphism (ringHomRange f hf) S :=
  RingIsomorphism.ofRingEquiv (ringHomRangeEquivOfSurjective f hf hsurj)

/-- 底层集合相等的双边理想给出本库显式商环之间的规范同构。
> **Entry**: abstract-algebra.ring.iso-theorems-/
private def quotientRingEquivOfEqualIdeals {R : Type*} [Ring R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (hEq : I = J) : RingEquiv (quotientRingSet I hI) (quotientRingSet J hJ) := by
  subst J
  have hp : hJ = hI := Subsingleton.elim _ _
  subst hJ
  exact RingEquiv.refl _

/-- 底层集合相等的双边理想给出显式商环之间的旧载体兼容同构。
> **Entry**: abstract-algebra.ring.iso-theorems-/
def quotientRingIsomorphismOfEqualIdeals {R : Type*} [Ring R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (hEq : I = J) : RingIsomorphism (quotientRingSet I hI) (quotientRingSet J hJ) :=
  RingIsomorphism.ofRingEquiv (quotientRingEquivOfEqualIdeals I J hI hJ hEq)

private theorem quotientRingEquivOfEqualIdeals_projection
    {R : Type*} [Ring R] (I J : Set R) (hI : TwoSidedIdealSet I)
    (hJ : TwoSidedIdealSet J) (hEq : I = J) (x : R) :
    quotientRingEquivOfEqualIdeals I J hI hJ hEq
      (quotientRingProjection I hI x) = quotientRingProjection J hJ x := by
  subst J
  have hp : hJ = hI := Subsingleton.elim _ _
  subst hJ
  rfl

@[simp] theorem quotientRingIsomorphismOfEqualIdeals_projection
    {R : Type*} [Ring R] (I J : Set R) (hI : TwoSidedIdealSet I)
    (hJ : TwoSidedIdealSet J) (hEq : I = J) (x : R) :
    quotientRingIsomorphismOfEqualIdeals I J hI hJ hEq
      (quotientRingProjection I hI x) = quotientRingProjection J hJ x := by
  exact quotientRingEquivOfEqualIdeals_projection I J hI hJ hEq x

/-- **第二同构定理（正式承载）**：对带幺环的子环 `A` 与双边理想 `I`，
`A/(A∩I) ≅ (A+I)/I`。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def ringSecondEquiv {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    RingEquiv
      (quotientRingSet (subringIdealIntersection A I).carrier
        (subringIdealIntersection A I).isTwoSided)
      (quotientRingSet (subringIdealInSum A I).carrier
        (subringIdealInSum A I).isTwoSided) := by
  let f := secondIsomorphismCanonicalMap A I
  let hf := secondIsomorphismCanonicalMap_is_ringHomomorphism A I
  let hsurj := secondIsomorphismCanonicalMap_surjective A I
  let K := subringIdealIntersection A I
  let e₀ : RingEquiv (quotientRingSet K.carrier K.isTwoSided)
      (quotientRingSet (ringHomKernelSet f) (ringHomKernelSet_isTwoSidedIdeal f hf)) :=
    quotientRingEquivOfEqualIdeals K.carrier (ringHomKernelSet f)
      K.isTwoSided (ringHomKernelSet_isTwoSidedIdeal f hf)
      (secondIsomorphismCanonicalMap_kernel A I).symm
  let e₁ := ringFirstEquiv f hf
  let e₂ := ringHomRangeEquivOfSurjective f hf hsurj
  exact (e₀.trans e₁).trans e₂

/-- 第二同构定理的旧载体兼容接口；证明由 `ringSecondEquiv` 拥有。
> **Entry**: abstract-algebra.ring.iso-theorems-/
noncomputable def ringSecondIsomorphism {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) :
    RingIsomorphism
      (quotientRingSet (subringIdealIntersection A I).carrier
        (subringIdealIntersection A I).isTwoSided)
      (quotientRingSet (subringIdealInSum A I).carrier
        (subringIdealInSum A I).isTwoSided) :=
  RingIsomorphism.ofRingEquiv (ringSecondEquiv A I)

/-- 正式第二同构的代表元公式：`a` 的左侧商类映到其在 `(A+I)/I` 中的自然商类。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem ringSecondEquiv_projection {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) (a : A) :
    ringSecondEquiv A I
      (quotientRingProjection (subringIdealIntersection A I).carrier
        (subringIdealIntersection A I).isTwoSided a) =
      quotientRingProjection (subringIdealInSum A I).carrier
        (subringIdealInSum A I).isTwoSided
        (subringIdealSumInclusion A I a) := by
  unfold ringSecondEquiv
  dsimp only
  simp only [RingEquiv.trans_apply]
  rw [quotientRingEquivOfEqualIdeals_projection, ringFirstEquiv_projection]
  rfl

/-- 旧第二同构兼容接口的代表元公式。
> **Entry**: abstract-algebra.ring.iso-theorems-/
@[simp] theorem ringSecondIsomorphism_projection {R : Type*} [Ring R]
    (A : SubringCarrier R) (I : TwoSidedIdealCarrier R) (a : A) :
    ringSecondIsomorphism A I
      (quotientRingProjection (subringIdealIntersection A I).carrier
        (subringIdealIntersection A I).isTwoSided a) =
      quotientRingProjection (subringIdealInSum A I).carrier
        (subringIdealInSum A I).isTwoSided
        (subringIdealSumInclusion A I a) := by
  exact ringSecondEquiv_projection A I a

end SandronesLibrary.AbstractAlgebra.Ring
