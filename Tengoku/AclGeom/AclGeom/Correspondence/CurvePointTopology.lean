/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.NormalCurveStalks
import Tengoku.Seed.RingTheory.KrullDimension.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed and generic points of actual integral curves

**Status:** proved for the actual topology of integral dimension-one schemes. Closed points
are exactly the nongeneric points; the actual stalk is a field exactly at the generic point.
Named consumer: the actual closed-point/place equivalence.

The given proper normal curve is an actual input. Projective presentation, joint regularity of
extended families, rational-action regularization and the full original classifier remain
owed, alongside group/chunk/six-point statements, algebraization/descent and every true
bypassed auxiliary. All eight original #21 work items and the full durable goal remain active
and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.CurvePointsPlaces
noncomputable section
open CategoryTheory AlgebraicGeometry
attribute [local instance] specializationOrder
universe u

/-- Closed points are the minimal elements of a scheme's specialization order.
Named consumer: identifying places with actual closed points of a curve.
@isnad1 id=iff.0h2v.s6.db89a91a192e from=translated src=- shape=3e3209bd vocab=e0d8ea37
-/
theorem isClosed_singleton_iff_isMin (X : Scheme.{u}) (x : X) :
    IsClosed ({x} : Set X) ↔ IsMin x := by
  constructor
  · intro hx y hy
    have hsp : x ⤳ y := hy
    have hmem := hsp.mem_closure
    rw [hx.closure_eq] at hmem
    exact le_of_eq (Set.mem_singleton_iff.mp hmem).symm
  · intro hx
    apply closure_eq_iff_isClosed.mp
    apply Set.Subset.antisymm _ subset_closure
    intro y hy
    have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
    exact Set.mem_singleton_iff.mpr (le_antisymm hyx (hx hyx))

/-- On an actual integral dimension-one curve, the closed points are exactly the
nongeneric points. Named consumer: the actual closed-point/place equivalence.
@isnad1 id=iff.1h2v.s7.baca8773eb33 from=translated src=- shape=ab46a01c vocab=7e2671fb
-/
theorem isClosed_singleton_iff_ne_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (x : X) :
    IsClosed ({x} : Set X) ↔ x ≠ genericPoint X := by
  have he : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm
  rw [isClosed_singleton_iff_isMin]
  constructor
  · intro hx h
    subst x
    change IsMin (⊤ : X) at hx
    have : Subsingleton X := subsingleton_of_forall_eq ⊤ fun a ↦
      le_antisymm le_top (hx le_top)
    have hz : Order.krullDim X = 0 := Order.krullDim_eq_zero
    exact (zero_ne_one : (0 : WithBot ℕ∞) ≠ 1) (hz.symm.trans (he.trans hdim))
  · intro hx
    exact (Order.krullDim_le_one_iff_forall_isMin.mp (he.trans hdim).le) x hx

/-- A stalk of an integral scheme is a field exactly at its generic point.
Named consumer: properness of the closed point's valuation subring.
@isnad1 id=iff.0h2v.s7.eebf6718c8cf from=translated src=- shape=f9756e91 vocab=2cea1ae9
-/
theorem isField_stalk_iff_genericPoint (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsField (X.presheaf.stalk x) ↔ x = genericPoint X := by
  constructor
  · intro hx
    have hc : (Order.coheight x : WithBot ℕ∞) = 0 :=
      (ringKrullDim_stalk_eq_coheight x).symm.trans (ringKrullDim_eq_zero_of_isField hx)
    have hc0 : Order.coheight x = 0 := by exact_mod_cast hc
    exact isMax_iff_eq_top.mp (Order.coheight_eq_zero.mp hc0)
  · rintro rfl
    exact (inferInstance : Field X.functionField).toIsField

end
end AclGeom.CurvePointsPlaces
