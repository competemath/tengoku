/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanHahnKaplansky.HahnKaplanskyRealClosedness.Basic.Cluster

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Odd-cluster hypotheses with coefficient properties

This module packages the common coefficient-condition shape used by subfield routes.  A route can
specialize `P` to a support, integrality, or other coefficient property without rebuilding the
odd-cluster projections in the specialized namespace.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Odd-cluster conditions together with a property of every polynomial coefficient.-/
def KOddClusterHypothesesWithCoeffProperty
    (P : HahnField k Γ → Prop)
    (F : Polynomial (HahnField k Γ)) (m : ℕ) : Prop :=
  0 < m ∧ Odd m ∧
    (∀ i, P (F.coeff i)) ∧
      (∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i)) ∧
        (∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i)) ∧
          addVal k Γ (F.coeff m) = 0

end HahnField

end

end HahnKaplanskyRealClosedness
