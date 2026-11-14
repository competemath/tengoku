/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.HomotopyStandard
import Tengoku.Seed.Topology.Homotopy.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 标准同伦等价

本模块把 Mathlib 的 `ContinuousMap.HomotopyEquiv` 解释为两张连续映射，其两个复合分别同伦于
相应恒等映射；同时记录等价关系运算及从同胚到同伦等价的桥。

当前条目：

* `topology.homotopy.equivalence-standard`.
-/

open ContinuousMap

namespace SandronesLibrary.Topology

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- 两个空间同伦等价，当且仅当存在两个方向的连续映射，并且两个复合分别同伦于相应恒等映射。

> **Entry**: topology.homotopy.equivalence-standard
@isnad1 id=iff.0h2v.s6.656a5134890b from=translated src=- shape=4bda29fe vocab=b3c33a85
-/
theorem nonempty_homotopyEquiv_iff_exists_two_sided_homotopy_inverse :
    Nonempty (X ≃ₕ Y) ↔
      ∃ f : C(X, Y), ∃ g : C(Y, X),
        (g.comp f).Homotopic (ContinuousMap.id X) ∧
        (f.comp g).Homotopic (ContinuousMap.id Y) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toFun, e.invFun, e.left_inv, e.right_inv⟩
  · rintro ⟨f, g, hleft, hright⟩
    exact ⟨{
      toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright
    }⟩

/-- 每个拓扑空间都同伦等价于自身。
@isnad1 id=nonempty.0h1v.s3.ff49c5d30b19 from=translated src=- shape=20cff623 vocab=bdbfc658
-/
theorem nonempty_homotopyEquiv_refl (X : Type u) [TopologicalSpace X] :
    Nonempty (X ≃ₕ X) :=
  ⟨ContinuousMap.HomotopyEquiv.refl X⟩

/-- 同伦等价的存在性具有对称性。
@isnad1 id=nonempty.1h2v.s4.1d71a7d107a2 from=translated src=- shape=03b81a4e vocab=bdbfc658
-/
theorem nonempty_homotopyEquiv_symm (h : Nonempty (X ≃ₕ Y)) :
    Nonempty (Y ≃ₕ X) :=
  h.map ContinuousMap.HomotopyEquiv.symm

/-- 同伦等价的存在性在复合下具有传递性。
@isnad1 id=nonempty.2h3v.s5.93d34db9b2b2 from=translated src=- shape=e7020d78 vocab=bdbfc658
-/
theorem nonempty_homotopyEquiv_trans
    (hXY : Nonempty (X ≃ₕ Y)) (hYZ : Nonempty (Y ≃ₕ Z)) :
    Nonempty (X ≃ₕ Z) :=
  hXY.map2 ContinuousMap.HomotopyEquiv.trans hYZ

/-- 同胚诱导的同伦等价具有完全相同的正向函数。
@isnad1 id=eq.0h4v.s6.5c9881ee38b1 from=translated src=- shape=f445dc39 vocab=0488fc53
-/
theorem homeomorph_toHomotopyEquiv_apply (e : X ≃ₜ Y) (x : X) :
    e.toHomotopyEquiv x = e x :=
  rfl

end SandronesLibrary.Topology
