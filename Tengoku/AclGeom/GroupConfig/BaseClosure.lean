/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.GroupConfig.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Replacing the base by its relative algebraic closure

Blueprint `sources/group_configuration/11-application.tex`, `rem:psi-hyp`(c): if `k` is not
algebraically closed, replace it by its relative algebraic closure `k̄ = acl_k(∅)` in `K`; this
changes neither the closed subfields, nor the points, nor the ranks of `𝒢(K/k)`.

* Relative algebraic closures over `k̄` and over `k` have the same carriers
  (`AclGeom.racl_baseClosure_coe`).
* Ranks over `k̄` and over `k` agree (`GroupConfig.erk_baseClosure`).
* The closed lattices are order isomorphic by an isomorphism preserving carriers
  (`AclGeom.ClosedIF.baseClosureEquiv`, `AclGeom.ClosedIF.coe_baseClosureEquiv`,
  `AclGeom.ClosedIF.coe_baseClosureEquiv_symm`).

Points correspond under `AclGeom.Point.map (AclGeom.ClosedIF.baseClosureEquiv k K)`, which keeps
carriers by `AclGeom.Point.map_coe`, and the lattice ranks `AclGeom.RankEq` agree by
`AclGeom.rankEq_map_iff`. Neither `K` nor `k` needs to be algebraically closed.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the base-closure invariance of `rem:psi-hyp`(c) is complete.
-/

open IntermediateField Set

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace AclGeom

/-- `rem:psi-hyp`(c): the relative algebraic closure of `S` over `k̄ = acl_k(∅)` is the relative
algebraic closure of `S` over `k`. Named consumer: `AclGeom.ClosedIF.baseClosureEquiv`.-/
theorem racl_baseClosure_coe (S : Set K) :
    ((racl (↥(racl k (∅ : Set K))) S : IntermediateField _ K) : Set K) = racl k S := by
  ext x
  have h : x ∈ racl (↥(racl k (∅ : Set K))) S ↔
      x ∈ racl k ((racl k (∅ : Set K) : Set K) ∪ S) := by
    rw [mem_racl_iff (↥(racl k (∅ : Set K))), mem_racl_iff k, ← restrictScalars_adjoin]
    exact Iff.rfl
  rw [SetLike.mem_coe, SetLike.mem_coe, h, racl_union_left, empty_union]

namespace ClosedIF

/-- A relatively algebraically closed field over `k̄` is relatively algebraically closed over
`k`. Named consumer: `AclGeom.ClosedIF.baseClosureEquiv`.-/
private theorem isRAC_restrictScalars {E : IntermediateField (↥(racl k (∅ : Set K))) K}
    (hE : IsRAC E) : IsRAC (E.restrictScalars k) := by
  rw [isRAC_iff_racl_eq] at hE ⊢
  refine SetLike.coe_injective ?_
  rw [coe_restrictScalars, ← racl_baseClosure_coe, hE]

/-- Every closed subfield over `k` contains `k̄`. Named consumer:
`AclGeom.ClosedIF.baseClosureEquiv`.-/
private theorem baseClosure_le (F : ClosedIF k K) : racl k (∅ : Set K) ≤ F.1 := by
  rw [← isRAC_iff_racl_eq.1 F.2]
  exact racl_mono (k := k) (empty_subset _)

/-- A closed subfield over `k` is relatively algebraically closed over `k̄`. Named consumer:
`AclGeom.ClosedIF.baseClosureEquiv`.-/
private theorem isRAC_extendScalars (F : ClosedIF k K) :
    IsRAC (extendScalars (baseClosure_le F)) := by
  rw [isRAC_iff_racl_eq]
  refine SetLike.coe_injective ?_
  rw [coe_extendScalars, racl_baseClosure_coe, isRAC_iff_racl_eq.1 F.2]

variable (k K) in
/-- `rem:psi-hyp`(c): the closed lattice over `k̄ = acl_k(∅)` is the closed lattice over `k`, by
an order isomorphism preserving carriers.-/
def baseClosureEquiv : ClosedIF (↥(racl k (∅ : Set K))) K ≃o ClosedIF k K where
  toFun E := ⟨E.1.restrictScalars k, isRAC_restrictScalars E.2⟩
  invFun F := ⟨extendScalars (baseClosure_le F), isRAC_extendScalars F⟩
  left_inv _ := Subtype.ext (SetLike.coe_injective rfl)
  right_inv _ := Subtype.ext (SetLike.coe_injective rfl)
  map_rel_iff' := Iff.rfl

/-- The order isomorphism `AclGeom.ClosedIF.baseClosureEquiv` preserves carriers.-/
@[simp]
theorem coe_baseClosureEquiv (E : ClosedIF (↥(racl k (∅ : Set K))) K) :
    ((baseClosureEquiv k K E : ClosedIF k K) : Set K) = E :=
  rfl

/-- The inverse of `AclGeom.ClosedIF.baseClosureEquiv` preserves carriers.-/
@[simp]
theorem coe_baseClosureEquiv_symm (F : ClosedIF k K) :
    (((baseClosureEquiv k K).symm F : ClosedIF (↥(racl k (∅ : Set K))) K) : Set K) = F :=
  rfl

end ClosedIF

end AclGeom

namespace GroupConfig

open AclGeom

end GroupConfig
