/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.MathlibBridge
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Constructions
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Path

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 旧教材拓扑与 Mathlib 拓扑的兼容层

旧 `TextbookTopology` 载体与 Mathlib 的 `TopologicalSpace` 在结构上等价。本模块提供迁移期间
使用的临时双向兼容层。新的拓扑学开发应直接使用 Mathlib 载体，不得仅为延续旧平行层级而先经过
`fromMathlib`。

当前条目：

* `topology.foundation.mathlib-compatibility`.
-/

namespace SandronesLibrary.Topology.TextbookTopology

variable {X Y : Type*}

set_option warn.classDefReducibility false in
/-- 把一个 Mathlib 拓扑看作具有完全相同开集的冻结旧教材载体。这是迁移桥，而不是拓扑空间的
新定义。

> **Entry**: topology.foundation.mathlib-compatibility-/
def fromMathlib (τ : TopologicalSpace X) : TextbookTopology X where
  IsOpen := @_root_.IsOpen X τ
  isOpen_univ := @_root_.isOpen_univ X τ
  isOpen_inter := fun s t ↦ @_root_.IsOpen.inter X τ s t
  isOpen_sUnion := @_root_.isOpen_sUnion X τ

/-- 反向桥在定义层面保持开集谓词不变。
@isnad1 id=iff.0h3v.s4.77aa74ffdc51 from=translated src=- shape=9f4602fa vocab=2a918ef3
-/
@[simp]
theorem isOpen_fromMathlib (τ : TopologicalSpace X) (s : Set X) :
    (fromMathlib τ).IsOpen s ↔ @_root_.IsOpen X τ s :=
  Iff.rfl

/-- Mathlib 拓扑转到旧载体再转回后，拓扑不变。
@isnad1 id=eq.0h2v.s3.77568208f089 from=translated src=- shape=efbf31f7 vocab=91a0c5d1
-/
@[simp]
theorem toMathlib_fromMathlib (τ : TopologicalSpace X) :
    (fromMathlib τ).toMathlib = τ := by
  apply TopologicalSpace.ext
  rfl

/-- 旧拓扑转到 Mathlib 再转回后，旧拓扑不变。
@isnad1 id=eq.0h2v.s3.983c64daaf4b from=translated src=- shape=efbf31f7 vocab=a2b64e09
-/
@[simp]
theorem fromMathlib_toMathlib (τ : TextbookTopology X) :
    fromMathlib τ.toMathlib = τ := by
  cases τ
  rfl

/-- 该桥也保持闭集：两侧的“闭”都表示补集是开集。
@isnad1 id=iff.0h3v.s4.e411d3b3e036 from=translated src=- shape=238e1b69 vocab=79afd90e
-/
@[simp]
theorem isClosed_toMathlib (τ : TextbookTopology X) (s : Set X) :
    @_root_.IsClosed X τ.toMathlib s ↔ τ.IsClosed s := by
  constructor
  · intro h
    exact h.isOpen_compl
  · intro h
    exact @IsClosed.mk X τ.toMathlib s h

/-- 安装同一个拓扑后，旧邻域谓词等价于属于 Mathlib 的邻域滤子。
@isnad1 id=iff.0h4v.s4.0008669884ab from=translated src=- shape=fc87ffb7 vocab=0f96cd01
-/
theorem isNeighborhood_iff_mem_nhds (τ : TextbookTopology X) (x : X) (s : Set X) :
    τ.IsNeighborhood x s ↔ s ∈ @nhds X τ.toMathlib x := by
  rw [@SandronesLibrary.Topology.mem_nhds_iff_exists_open X τ.toMathlib x s]
  rfl

/-- 冻结的旧拓扑载体与 Mathlib 拓扑载体结构等价。

这个等价只用于迁移旧声明，不能据此把面向 Mathlib 的新定理搬回旧层级。-/
def equivMathlib : TextbookTopology X ≃ TopologicalSpace X where
  toFun := toMathlib
  invFun := fromMathlib
  left_inv := fromMathlib_toMathlib
  right_inv := toMathlib_fromMathlib

/-- 旧诱导拓扑转到 Mathlib 后，严格等于 Mathlib 的规范诱导拓扑。
@isnad1 id=eq.0h4v.s4.28d0d757c637 from=translated src=- shape=2049033c vocab=184f1da0
-/
theorem toMathlib_induced (f : X → Y) (τY : TextbookTopology Y) :
    (induced f τY).toMathlib = TopologicalSpace.induced f τY.toMathlib := by
  apply TopologicalSpace.ext
  rfl

/-- 旧子空间拓扑转到 Mathlib 后，严格等于 subtype 的规范拓扑实例。
@isnad1 id=eq.0h3v.s4.0abaa75e175a from=translated src=- shape=da605417 vocab=2c159ff8
-/
theorem toMathlib_subspace (s : Set X) (τX : TextbookTopology X) :
    (subspace s τX).toMathlib = @instTopologicalSpaceSubtype X s τX.toMathlib := by
  apply TopologicalSpace.ext
  rfl

/-- 旧积拓扑转到 Mathlib 后，严格等于积类型的规范拓扑实例。
@isnad1 id=eq.0h4v.s5.0d8a66a5b386 from=translated src=- shape=7ebf9757 vocab=b045a084
-/
theorem toMathlib_product (τX : TextbookTopology X) (τY : TextbookTopology Y) :
    (product τX τY).toMathlib = @instTopologicalSpaceProd X Y τX.toMathlib τY.toMathlib := by
  apply TopologicalSpace.ext
  funext s
  apply propext
  let _ := τX.toMathlib
  let _ := τY.toMathlib
  rw [SandronesLibrary.Topology.isOpen_prod_iff_rectangles]
  constructor
  · intro h x y hxy
    obtain ⟨u, v, hu, hv, hmem, hsub⟩ := h (x, y) hxy
    exact ⟨u, v, hu, hv, hmem.1, hmem.2, hsub⟩
  · intro h p hp
    obtain ⟨u, v, hu, hv, hpu, hpv, hsub⟩ := h p.1 p.2 hp
    exact ⟨u, v, hu, hv, ⟨hpu, hpv⟩, hsub⟩

/-- 旧 ε 邻域实拓扑转到 Mathlib 后，严格等于标准实数拓扑实例。
@isnad1 id=eq.0h0v.s3.fa34161a2fab from=translated src=- shape=687008b2 vocab=5fd70b53
-/
theorem toMathlib_realLine :
    realLine.toMathlib = (inferInstance : TopologicalSpace ℝ) := by
  apply TopologicalSpace.ext
  funext s
  apply propext
  rw [SandronesLibrary.Topology.real_isOpen_iff_abs]
  rfl

/-- 旧单位区间拓扑转到 Mathlib 后，严格等于闭区间 subtype 的规范拓扑实例。
@isnad1 id=eq.0h0v.s5.bc1a40805d5b from=translated src=- shape=53886065 vocab=d80589ac
-/
theorem toMathlib_unitInterval :
    unitInterval.toMathlib =
      @instTopologicalSpaceSubtype ℝ (fun t ↦ 0 ≤ t ∧ t ≤ 1)
        (inferInstance : TopologicalSpace ℝ) := by
  unfold unitInterval UnitInterval
  rw [toMathlib_subspace, toMathlib_realLine]

namespace Path

/-- 把旧道路转换为同一拓扑上的 Mathlib 道路，保持参数函数与两个端点不变。-/
def toMathlib {τX : TextbookTopology X} {a b : X}
    (γ : Path τX a b) : @_root_.Path X τX.toMathlib a b := by
  let _ := τX.toMathlib
  have hγ : @_root_.Continuous UnitInterval X unitInterval.toMathlib τX.toMathlib γ :=
    (continuous_iff_mathlib unitInterval τX γ).mp γ.continuous
  rw [toMathlib_unitInterval] at hγ
  exact { toFun := γ, continuous_toFun := hγ, source' := γ.source, target' := γ.target }

/-- 把桥接拓扑上的 Mathlib 道路转换为旧道路，保持参数函数与两个端点不变。-/
def fromMathlib {τX : TextbookTopology X} {a b : X}
    (γ : @_root_.Path X τX.toMathlib a b) : Path τX a b := by
  let _ := τX.toMathlib
  have hγ : @_root_.Continuous UnitInterval X unitInterval.toMathlib τX.toMathlib γ := by
    rw [toMathlib_unitInterval]
    exact γ.continuous
  exact {
    toFun := γ
    continuous := (continuous_iff_mathlib unitInterval τX γ).mpr hγ
    source := γ.source
    target := γ.target }

/-- 旧道路转到 Mathlib 再转回后不变。
@isnad1 id=eq.0h5v.s5.f5f79c0971f2 from=translated src=- shape=e4d00c35 vocab=d323f455
-/
@[simp]
theorem fromMathlib_toMathlib {τX : TextbookTopology X} {a b : X} (γ : Path τX a b) :
    fromMathlib (toMathlib γ) = γ := by
  apply Path.ext
  intro t
  change γ t = γ t
  rfl

/-- Mathlib 道路转到旧载体再转回后不变。
@isnad1 id=eq.0h5v.s5.2106113be360 from=translated src=- shape=5759a1be vocab=cfa16a7f
-/
@[simp]
theorem toMathlib_fromMathlib {τX : TextbookTopology X} {a b : X}
    (γ : @_root_.Path X τX.toMathlib a b) :
    toMathlib (fromMathlib γ) = γ := by
  let _ := τX.toMathlib
  apply _root_.Path.ext
  change (γ : UnitInterval → X) = γ
  rfl

/-- 旧道路转到 Mathlib 的转换与道路反向交换。
@isnad1 id=eq.0h5v.s5.e0c54231184a from=translated src=- shape=f22ed424 vocab=6fcfe132
-/
theorem toMathlib_symm {τX : TextbookTopology X} {a b : X} (γ : Path τX a b) :
    toMathlib γ.symm =
      @_root_.Path.symm X τX.toMathlib a b (toMathlib γ) := by
  let _ := τX.toMathlib
  apply _root_.Path.ext
  funext t
  rfl

/-- 旧道路转到 Mathlib 的转换与道路拼接交换。
@isnad1 id=eq.0h7v.s6.859324be7c4e from=translated src=- shape=f4f32452 vocab=c84d8226
-/
theorem toMathlib_trans {τX : TextbookTopology X} {a b c : X}
    (γ : Path τX a b) (δ : Path τX b c) :
    toMathlib (γ.trans δ) =
      @_root_.Path.trans X τX.toMathlib a b c (toMathlib γ) (toMathlib δ) := by
  let _ := τX.toMathlib
  apply _root_.Path.ext
  funext t
  rw [_root_.Path.trans_apply]
  rfl

end Path

namespace Homeomorphism

variable {Y : Type*}

/-- 底层集合等价相同的两个旧同胚相等。
@isnad1 id=eq.1h6v.s5.4bbc267d21e0 from=translated src=- shape=21eea939 vocab=99e10abc
-/
theorem ext {τX : TextbookTopology X} {τY : TextbookTopology Y}
    {e e' : Homeomorphism τX τY} (h : e.toEquiv = e'.toEquiv) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

/-- 把旧同胚转换为 Mathlib 的正式 `Homeomorph` 承载。-/
def toMathlib {τX : TextbookTopology X} {τY : TextbookTopology Y}
    (e : Homeomorphism τX τY) :
    @Homeomorph X Y τX.toMathlib τY.toMathlib :=
  @Homeomorph.mk X Y τX.toMathlib τY.toMathlib e.toEquiv
    ((continuous_iff_mathlib τX τY _).mp e.continuous_toFun)
    ((continuous_iff_mathlib τY τX _).mp e.continuous_invFun)

/-- 把桥接拓扑之间的 Mathlib 同胚转换到旧载体。-/
def fromMathlib {τX : TextbookTopology X} {τY : TextbookTopology Y}
    (e : @Homeomorph X Y τX.toMathlib τY.toMathlib) :
    Homeomorphism τX τY := by
  let _ := τX.toMathlib
  let _ := τY.toMathlib
  exact {
    toEquiv := e.toEquiv
    continuous_toFun := (continuous_iff_mathlib τX τY _).mpr e.continuous
    continuous_invFun := (continuous_iff_mathlib τY τX _).mpr e.symm.continuous }

/-- 旧同胚转到 Mathlib 再转回后，数据不变。
@isnad1 id=eq.0h5v.s5.79e19e07a59c from=translated src=- shape=b40cf5f3 vocab=2304ab80
-/
@[simp]
theorem fromMathlib_toMathlib {τX : TextbookTopology X} {τY : TextbookTopology Y}
    (e : Homeomorphism τX τY) : fromMathlib (toMathlib e) = e := by
  apply ext
  rfl

/-- Mathlib 同胚转到旧载体再转回后，数据不变。
@isnad1 id=eq.0h5v.s5.6b9d57ed6dd5 from=translated src=- shape=f9365c53 vocab=dd0273b3
-/
@[simp]
theorem toMathlib_fromMathlib {τX : TextbookTopology X} {τY : TextbookTopology Y}
    (e : @Homeomorph X Y τX.toMathlib τY.toMathlib) :
    toMathlib (fromMathlib e) = e := by
  let _ := τX.toMathlib
  let _ := τY.toMathlib
  apply _root_.Homeomorph.ext
  intro x
  change e x = e x
  rfl

end Homeomorphism

end SandronesLibrary.Topology.TextbookTopology
