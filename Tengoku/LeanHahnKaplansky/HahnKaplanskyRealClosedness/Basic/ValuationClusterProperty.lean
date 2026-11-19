/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanHahnKaplansky.HahnKaplanskyRealClosedness.Basic.ClusterProperty
import Tengoku.LeanHahnKaplansky.HahnKaplanskyRealClosedness.Basic.LocalClusterProperty

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation-subring cluster hypotheses with coefficient properties

This module contains the common packaging for valuation-subring cluster routes.  The coefficient
property is abstract so subfields can reuse the same odd, one-cluster, and monic projections.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Valuation-subring odd-cluster conditions with a property of every Hahn-field coefficient.

This is only the valuation-subring specialization of the local-ring package; keeping the name
preserves the existing Hahn-field API for downstream routes.-/
abbrev ValuationSubringOddClusterHypothesesWithCoeffProperty
    (P : HahnField k Γ → Prop)
    (F : Polynomial (valuationSubring k Γ)) (m : ℕ) : Prop :=
  LocalOddClusterHypothesesWithCoeffProperty
    (R := valuationSubring k Γ) (fun x => P (x : HahnField k Γ)) F m

/-- The `m = 1` specialization of a valuation-subring odd-cluster package.-/
abbrev ValuationSubringOneClusterHypothesesWithCoeffProperty
    (P : HahnField k Γ → Prop)
    (F : Polynomial (valuationSubring k Γ)) : Prop :=
  LocalOneClusterHypothesesWithCoeffProperty
    (R := valuationSubring k Γ) (fun x => P (x : HahnField k Γ)) F

theorem ValuationSubringOneClusterHypothesesWithCoeffProperty.oddClusterHypotheses
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)}
    (h : ValuationSubringOneClusterHypothesesWithCoeffProperty k Γ P F) :
    ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F 1 :=
  LocalOneClusterHypothesesWithCoeffProperty.oddClusterHypotheses h

end HahnField

end

end HahnKaplanskyRealClosedness
