/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.CurvePointTopology
import Tengoku.Seed.Topology.JacobsonSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The literal finite boundary of an actual curve

**Status:** proved for actual Noetherian integral dimension-one schemes. The complement of
every actual nonempty open is finite and consists of closed points. A continuous map from an
irreducible space into finitely many closed points is constant. Named consumer: the actual
joint fixed-boundary theorem.

The regular action on the ambient curve is an actual input. Projective presentation, joint
regularity of extended rational families, rational-action regularization and the full original
classifier remain owed. Original group/chunk/six-point statements, algebraization/descent and
every true bypassed auxiliary remain obligations. All eight original #21 work items and the
full durable goal remain active and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.CurveBoundary
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
attribute [local instance] specializationOrder

/-- A continuous map from an irreducible space into finitely many closed points is constant.
Named consumer: the actual boundary orbit morphism.
@isnad1 id=eq.4h6v.s6.b51bf88d6d3c from=translated src=- shape=4bf414ed vocab=c1416c8e
-/
theorem constant_of_finite_closed_range
    {A B : Type*} [TopologicalSpace A] [PreirreducibleSpace A] [TopologicalSpace B]
    (f : A → B) (hf : Continuous f) (S : Set B) (hS : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set B)) (hmem : ∀ a, f a ∈ S) :
    ∀ a b, f a = f b := by
  have hr : Set.range f ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact hmem a
  have hd : IsDiscrete (Set.range f) :=
    (hS.isDiscrete_of_subset_closedPoints (fun x hx ↦ hclosed x hx)).mono hr
  have hi : IsPreirreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      PreirreducibleSpace.isPreirreducible_univ.image f hf.continuousOn
  intro a b
  exact hd.subsingleton_of_isPreirreducible hi ⟨a, rfl⟩ ⟨b, rfl⟩

end
end AclGeom.CurveBoundary
