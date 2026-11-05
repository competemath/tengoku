/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.Topology.Algebra.ClopenNhdofOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Open subgroups of compact groups

This module records openness and closedness properties of open (normal) subgroups, constructs
their pullbacks, and proves that they have finite index in compact topological groups.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups

universe u v

section OpenSubgroups

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- An open subgroup is open as a subset.
@isnad1 id=isopen.0h2v.s4.a962ca2f1314 from=translated src=- shape=b82487ba vocab=d51c2aa1
-/
theorem openSubgroup_isOpen (U : OpenSubgroup G) :
    IsOpen ((U : Subgroup G) : Set G) := by
  exact U.isOpen

/-- An open subgroup is closed as a subset.
@isnad1 id=isclosed.0h2v.s5.0a29560bf035 from=translated src=- shape=e20b88b0 vocab=c203643b
-/
theorem openSubgroup_isClosed [ContinuousMul G] (U : OpenSubgroup G) :
    IsClosed ((U : Subgroup G) : Set G) := by
  exact OpenSubgroup.isClosed U

/-- An open normal subgroup is open as a subset.
@isnad1 id=isopen.0h2v.s5.79f9eb2e3213 from=translated src=- shape=88675009 vocab=ec6d08a2
-/
theorem openNormalSubgroup_isOpen (U : OpenNormalSubgroup G) :
    IsOpen ((U : Subgroup G) : Set G) := by
  exact U.toOpenSubgroup.isOpen

/-- An open normal subgroup is closed as a subset.
@isnad1 id=isclosed.0h2v.s5.56c7b0e7ea0c from=translated src=- shape=63d3a488 vocab=51d58065
-/
theorem openNormalSubgroup_isClosed [ContinuousMul G] (U : OpenNormalSubgroup G) :
    IsClosed ((U : Subgroup G) : Set G) := by
  exact OpenSubgroup.isClosed U.toOpenSubgroup

namespace OpenNormalSubgroup

/-- Pull back an open normal subgroup along a continuous homomorphism.-/
def comap {H : Type v} [Group H] [TopologicalSpace H]
    (f : G →* H) (hf : Continuous f) (U : OpenNormalSubgroup H) : OpenNormalSubgroup G :=
  { toOpenSubgroup := U.toOpenSubgroup.comap f hf
    isNormal' := by
      change ((U : Subgroup H).comap f).Normal
      infer_instance }

/-- The subgroup underlying the comap of an open subgroup is the subgroup comap.
@isnad1 id=eq.1h4v.s7.7435b30a13a8 from=translated src=- shape=ff9d6114 vocab=ff7ac80c
-/
@[simp, norm_cast]
theorem toSubgroup_comap {H : Type v} [Group H] [TopologicalSpace H]
    (f : G →* H) (hf : Continuous f) (U : OpenNormalSubgroup H) :
    ((OpenNormalSubgroup.comap f hf U : OpenNormalSubgroup G) : Subgroup G) =
      (U : Subgroup H).comap f :=
  rfl

/-- Membership in the comap of an open subgroup is membership after applying the homomorphism.
@isnad1 id=iff.1h5v.s7.56f46992b31b from=translated src=- shape=0dab2a36 vocab=4a24ce00
-/
@[simp]
theorem mem_comap {H : Type v} [Group H] [TopologicalSpace H]
    {f : G →* H} {hf : Continuous f} {U : OpenNormalSubgroup H} {x : G} :
    x ∈ OpenNormalSubgroup.comap f hf U ↔ f x ∈ U :=
  Iff.rfl

end OpenNormalSubgroup

/--
An open subgroup of a compact topological group has finite coset space, equivalently finite
index.
@isnad1 id=finite.0h2v.s5.073c892a3386 from=translated src=- shape=d943d760 vocab=4bf899a8
-/
theorem openSubgroup_finiteQuotient [ContinuousMul G] [CompactSpace G]
    (U : OpenSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) := by
  exact Subgroup.quotient_finite_of_isOpen (U : Subgroup G) (openSubgroup_isOpen (G := G) U)

/-- Any open normal subgroup of a compact topological group has finite quotient.
@isnad1 id=finite.0h2v.s5.ff477403ab08 from=translated src=- shape=20d9ac1c vocab=647ec5a7
-/
theorem openNormalSubgroup_finiteQuotient [ContinuousMul G] [CompactSpace G]
    (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) := by
  exact Subgroup.quotient_finite_of_isOpen (U : Subgroup G)
    (openNormalSubgroup_isOpen (G := G) U)

/-- In a compact topological group, every element has a positive power in any open subgroup.
@isnad1 id=ex.0h3v.s6.bafe96ca17df from=translated src=- shape=2c52feab vocab=ac77c6f4
-/
theorem exists_pos_pow_mem_openSubgroup [ContinuousMul G] [CompactSpace G]
    (U : OpenSubgroup G) (g : G) :
    ∃ n : ℕ, 0 < n ∧ g ^ n ∈ (U : Subgroup G) := by
  let K : Subgroup G := (U : Subgroup G).normalCore
  let : Finite (G ⧸ (U : Subgroup G)) :=
    openSubgroup_finiteQuotient (G := G) U
  let : (U : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let : K.FiniteIndex := Subgroup.finiteIndex_normalCore (H := (U : Subgroup G))
  have hidx : K.index ≠ 0 := (Subgroup.finiteIndex_iff (H := K)).mp ‹K.FiniteIndex›
  refine ⟨K.index, Nat.pos_iff_ne_zero.mpr hidx, ?_⟩
  exact (Subgroup.normalCore_le (U : Subgroup G)) (K.pow_index_mem g)

/--
In a compact topological group, a subgroup is open if and only if it is closed and the quotient
is finite. Equivalently, the subgroup is closed of finite index; in this version, Finite
(\(G/U\)) is the most direct encoding of finite index.
@isnad1 id=iff.0h2v.s6.e14baf037d63 from=translated src=- shape=ebb81a6a vocab=427e5c25
-/
theorem subgroup_isOpen_iff_isClosed_finite_quotient [ContinuousMul G] [CompactSpace G]
    {U : Subgroup G} :
    IsOpen (U : Set G) ↔ IsClosed (U : Set G) ∧ Finite (G ⧸ U) := by
  constructor
  · intro hU
    exact ⟨Subgroup.isClosed_of_isOpen U hU, Subgroup.quotient_finite_of_isOpen U hU⟩
  · rintro ⟨hUclosed, hUfinite⟩
    let : IsClosed (U : Set G) := hUclosed
    let : Finite (G ⧸ U) := hUfinite
    exact (QuotientGroup.discreteTopology_iff (N := U)).1
      (inferInstance : DiscreteTopology (G ⧸ U))

end OpenSubgroups

end ProCGroups
