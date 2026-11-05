/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.AlgebraicGeometry.FunctionField
import Tengoku.Seed.AlgebraicGeometry.Noetherian
import Tengoku.Seed.RingTheory.DiscreteValuationRing.TFAE

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation-ring stalks of normal curves

**Status:** proved for integral locally Noetherian schemes of dimension at most one with
actual integrally closed stalks. The actual scheme dimension bounds every stalk dimension; the
local Dedekind/PID API gives a valuation ring, including the generic field stalk. Named
consumer: unique extension of rational maps to proper targets.

For a given actual proper normal integral dimension-one curve, the closed-point/place
identification is now proved by CurvePointsPlaces.exists_point_place_model, including actual
stalk ring equivalences and automorphism compatibility. The given proper normal curve is an
actual input. Projective presentation, joint regularity of extended families, rational-action
regularization and the full original classifier remain owed, alongside group/chunk/six-point
statements, algebraization/descent and every true bypassed auxiliary. All eight original #21
work items and the full durable goal remain active and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.ProperCurve
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- Normal locally Noetherian integral curves have valuation-ring stalks.
Named consumer: extension of rational maps to proper targets.
@isnad1 id=valuatio.1h2v.s7.e8a67fdb1238 from=translated src=- shape=2e8e24bf vocab=4364036f
-/
theorem stalk_valuationRing
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] :
    ValuationRing (X.presheaf.stalk x) := by
  have he : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := X))).symm
  have hco : (Order.coheight x : WithBot ℕ∞) ≤ 1 :=
    (Order.coheight_le_krullDim x).trans (he.trans_le hdim)
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    krullDimLE_of_coheight_le (by exact_mod_cast hco)
  have : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    ⟨fun hI hP ↦ Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance _ hI hP⟩
  have : IsDedekindDomain (X.presheaf.stalk x) :=
    (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk x))).2
      ⟨inferInstance, inferInstance, inferInstance,
        fun hz ↦ (isIntegrallyClosed_iff _).1 inferInstance hz⟩
  infer_instance

end
end AclGeom.ProperCurve
