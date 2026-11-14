/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathHomotopyStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 道路同伦商的标准承载

本文件直接采用 Mathlib 的 `Path.Homotopic.Quotient`，并把商类相等展开为端点固定的连续正方形
变形。新接口不经过冻结的 `TextbookTopology` 同伦或旧道路商。

当前条目：

* `topology.homotopy.path-homotopy-quotient-standard`。
-/

namespace SandronesLibrary.Topology

universe u

variable {X : Type u} [TopologicalSpace X]
variable {x y : X}

/-- 两条道路代表同一个道路同伦商类，当且仅当它们之间存在连续的端点固定变形。第一坐标是
同伦时间，第二坐标是道路参数。

> **Entry**: topology.homotopy.path-homotopy-quotient-standard-/
theorem pathHomotopyQuotient_mk_eq_iff_exists_fixed_endpoint_deformation
    {p q : Path x y} :
    Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q ↔
      ∃ F : unitInterval × unitInterval → X, Continuous F ∧
        (∀ s, F (0, s) = p s) ∧
        (∀ s, F (1, s) = q s) ∧
        (∀ t, F (t, 0) = x) ∧
        (∀ t, F (t, 1) = y) := by
  rw [Path.Homotopic.Quotient.eq]
  exact nonempty_pathHomotopy_iff_exists_fixed_endpoint_deformation

/-- Mathlib 的简洁关系接口与道路同伦商的判等完全一致。-/
theorem pathHomotopyQuotient_mk_eq_iff_homotopic {p q : Path x y} :
    Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q ↔ p.Homotopic q :=
  Path.Homotopic.Quotient.eq

/-- 每个道路同伦商类都有一条实际道路作为代表。代表一般不唯一，恰由道路同伦关系判等。-/
theorem pathHomotopyQuotient_exists_representative
    (P : Path.Homotopic.Quotient x y) :
    ∃ p : Path x y, Path.Homotopic.Quotient.mk p = P := by
  exact Path.Homotopic.Quotient.mk_surjective P

end SandronesLibrary.Topology
