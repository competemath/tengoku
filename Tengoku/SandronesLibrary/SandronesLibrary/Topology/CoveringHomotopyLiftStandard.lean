/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.CoveringPathLiftStandard
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.HomotopyStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 覆盖映射的同伦提升

本模块直接复用 Mathlib `IsCoveringMap.liftHomotopy`：给定参数化同伦以及其时间零切片在总空间中的
连续提升，得到整个参数柱上的唯一连续提升。提升的时间一切片由构造决定，并进一步把同一个连续映射
薄封装为本库采用的标准 `ContinuousMap.Homotopy`。

当前条目：

* `topology.covering.homotopy-lifting-standard`。

这里不从逐点道路提升重新拼装二维提升，不另造同伦 carrier，也不处理 relative lifting、monodromy
或覆盖空间分类。
-/

open Function
open scoped unitInterval

namespace SandronesLibrary.Topology

universe u v w

variable {E : Type u} {X : Type v} {A : Type w}
variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
variable {p : E → X}

/-- 基同伦及其时间零切片的连续提升，唯一决定整个参数柱上的连续提升。

> **Entry**: topology.covering.homotopy-lifting-standard-/
theorem existsUnique_coveringMap_homotopyLift
    (cov : IsCoveringMap p) (H : C(unitInterval × A, X))
    (f0Lift : C(A, E)) (H0 : ∀ a, H (0, a) = p (f0Lift a)) :
    ∃! Hlift : C(unitInterval × A, E),
      p ∘ Hlift = H ∧ ∀ a, Hlift (0, a) = f0Lift a := by
  refine ⟨cov.liftHomotopy H f0Lift H0,
    ⟨cov.liftHomotopy_lifts H f0Lift H0,
      cov.liftHomotopy_zero H f0Lift H0⟩, ?_⟩
  intro Hlift hHlift
  exact (cov.eq_liftHomotopy_iff' H0 Hlift).mpr hHlift

/-- 提升同伦的时间一切片，作为参数空间到总空间的连续映射。-/
noncomputable def coveringMapHomotopyLiftEndpoint
    (cov : IsCoveringMap p) {f0 f1 : C(A, X)} (F : f0.Homotopy f1)
    (f0Lift : C(A, E)) (hf0 : p ∘ f0Lift = f0) : C(A, E) :=
  let H0 : ∀ a, F (0, a) = p (f0Lift a) :=
    fun a => (F.apply_zero a).trans (congr_fun hf0 a).symm
  ⟨fun a => cov.liftHomotopy F f0Lift H0 (1, a),
    by fun_prop⟩

/-- 从指定时间零提升出发的标准同伦；终点是提升在时间一决定的连续映射。-/
noncomputable def coveringMapHomotopyLift
    (cov : IsCoveringMap p) {f0 f1 : C(A, X)} (F : f0.Homotopy f1)
    (f0Lift : C(A, E)) (hf0 : p ∘ f0Lift = f0) :
    f0Lift.Homotopy (coveringMapHomotopyLiftEndpoint cov F f0Lift hf0) := by
  let H0 : ∀ a, F (0, a) = p (f0Lift a) :=
    fun a => (F.apply_zero a).trans (congr_fun hf0 a).symm
  exact {
    toContinuousMap := cov.liftHomotopy F f0Lift H0
    map_zero_left := cov.liftHomotopy_zero F f0Lift H0
    map_one_left := fun _ => rfl
  }

/-- 标准提升同伦经覆盖映射逐点投影回原同伦。-/
theorem coveringMapHomotopyLift_lifts
    (cov : IsCoveringMap p) {f0 f1 : C(A, X)} (F : f0.Homotopy f1)
    (f0Lift : C(A, E)) (hf0 : p ∘ f0Lift = f0)
    (z : unitInterval × A) :
    p (coveringMapHomotopyLift cov F f0Lift hf0 z) = F z := by
  let H0 : ∀ a, F (0, a) = p (f0Lift a) :=
    fun a => (F.apply_zero a).trans (congr_fun hf0 a).symm
  exact congr_fun (cov.liftHomotopy_lifts F f0Lift H0) z

/-- 提升同伦的时间一切片经覆盖映射投影为原同伦的时间一映射。-/
theorem coveringMapHomotopyLiftEndpoint_lifts
    (cov : IsCoveringMap p) {f0 f1 : C(A, X)} (F : f0.Homotopy f1)
    (f0Lift : C(A, E)) (hf0 : p ∘ f0Lift = f0) (a : A) :
    p (coveringMapHomotopyLiftEndpoint cov F f0Lift hf0 a) = f1 a :=
  (coveringMapHomotopyLift_lifts cov F f0Lift hf0 (1, a)).trans (F.apply_one a)

end SandronesLibrary.Topology
