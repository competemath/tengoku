/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Data.Int.WithZero
import Tengoku.Seed.Topology.Algebra.Valued.ValuationTopology
import Tengoku.Seed.Topology.Algebra.Group.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuity of valuation-preserving field automorphisms

A valuation-preserving automorphism preserves every basic neighbourhood of
zero for the actual topology induced by the valuation. No completeness or
discreteness hypothesis is required.
-/

namespace ValuationTheory.DiscreteValuationField.Valuation

open scoped Topology

variable {K : Type*} [Field K]

/-- A valuation-preserving field automorphism is continuous for the topology
induced by that valuation.
@isnad1 id=continuo.1h3v.s9.8dc455594202 from=translated src=- shape=1af2c9cf vocab=c055a8e1
-/
theorem continuous_ringEquiv_of_preserves
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (f : K ≃+* K) (hval : ∀ x : K, v (f x) = v x) :
    @Continuous K K (Valued.mk' v).toUniformSpace.toTopologicalSpace
      (Valued.mk' v).toUniformSpace.toTopologicalSpace f := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  apply continuous_of_tendsto_nhds_zero f
  rw [(Valued.hasBasis_nhds_zero K (WithZero (Multiplicative ℤ))).tendsto_iff
    (Valued.hasBasis_nhds_zero K (WithZero (Multiplicative ℤ)))]
  intro γ _
  refine ⟨γ, trivial, ?_⟩
  intro x hx
  change v.restrict (f x) < γ.val
  rw [v.restrict_inj.mpr (hval x)]
  exact hx

end ValuationTheory.DiscreteValuationField.Valuation
