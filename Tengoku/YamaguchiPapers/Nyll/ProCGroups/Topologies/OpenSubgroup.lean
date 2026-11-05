/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Topology.Algebra.OpenSubgroup
import Tengoku.Seed.Topology.Algebra.ContinuousMonoidHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The whole group as an open subgroup

This file records the canonical continuous multiplicative equivalence between a topological group
and the subtype of its top open subgroup, together with its forward and inverse formulas.
-/

open scoped Topology

namespace ProCGroups

namespace OpenSubgroup

universe u

/-- The \(\top\) open subgroup is canonically equivalent to the ambient topological group.-/
noncomputable def topContinuousMulEquiv
    (G : Type u) [TopologicalSpace G] [Group G] :
    ↥((⊤ : OpenSubgroup G) : Subgroup G) ≃ₜ* G :=
  { toMulEquiv :=
      { toFun := fun x => x.1
        invFun := fun x => ⟨x, by simp only [_root_.OpenSubgroup.toSubgroup_top, Subgroup.mem_top]⟩
        left_inv := by
          intro x
          ext
          rfl
        right_inv := by
          intro x
          rfl
        map_mul' := by
          intro x y
          rfl }
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      exact Continuous.subtype_mk continuous_id (by intro x; simp only
          [_root_.OpenSubgroup.toSubgroup_top, id_eq, Subgroup.mem_top]) }

/-- The open-subgroup comparison equivalence evaluates on representatives.
@isnad1 id=eq.0h2v.s8.669a008131a4 from=translated src=- shape=b15fa1cb vocab=acacdb72
-/
@[simp] theorem topContinuousMulEquiv_apply
    (G : Type u) [TopologicalSpace G] [Group G]
    (x : ↥((⊤ : OpenSubgroup G) : Subgroup G)) :
    topContinuousMulEquiv G x = x.1 :=
  rfl

/--
The inverse comparison equivalence is evaluated by the same coordinate data, read in the
opposite direction.
@isnad1 id=eq.0h2v.s9.b92bdcff08f7 from=translated src=- shape=579fa40c vocab=3e4036c0
-/
@[simp] theorem topContinuousMulEquiv_symm_apply
    (G : Type u) [TopologicalSpace G] [Group G] (x : G) :
    (topContinuousMulEquiv G).symm x = ⟨x, by simp only [_root_.OpenSubgroup.toSubgroup_top,
        Subgroup.mem_top]⟩ :=
  rfl

end OpenSubgroup

end ProCGroups
