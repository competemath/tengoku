/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.PellFamily
import Tengoku.Goemans.Goemans.Rybin
import Tengoku.Goemans.Goemans.TheoremA
import Tengoku.Seed.Topology.Order.OrderClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The exact supremum on `H*`

The upper bound from `Goemans.TheoremA` and the explicit computable Pell family
from `Goemans.PellFamily` identify the supremum of all positive-cost ratios
with `ρ*`.
-/

namespace Goemans

noncomputable section

open Filter
open scoped Topology

namespace PositiveCostInstance

/-- Every individual positive-cost instance has ratio strictly below `ρ*`.
@isnad1 id=lt.0h1v.s3.163803018d66 from=translated src=- shape=f0bb1bdd vocab=788f3bb2
-/
theorem ratio_lt_rhoStar (I : PositiveCostInstance) :
    I.ratio < rhoStar := by
  obtain ⟨S, hS, hcost⟩ := I.1.exists_admissible_ucost_lt I.2
  rw [ratio, div_lt_iff₀ I.2]
  exact lt_of_le_of_lt (I.1.optimalUCost_le hS) hcost

/--
@isnad1 id=le.0h1v.s3.0c76985a2666 from=translated src=- shape=f0bb1bdd vocab=45202a6c
-/
theorem ratio_le_rhoStar (I : PositiveCostInstance) :
    I.ratio ≤ rhoStar :=
  I.ratio_lt_rhoStar.le

end PositiveCostInstance

/-- `ρ*` is the least upper bound of all positive-cost ratios on `H*`.
@isnad1 id=islub.0h0v.s2.d47747fde011 from=translated src=- shape=54c8eceb vocab=f80a0410
-/
theorem hStarRatios_isLUB : IsLUB hStarRatios rhoStar := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨I, rfl⟩
    exact I.ratio_le_rhoStar
  · intro a ha
    exact le_of_tendsto tendsto_pellFamily_ratio
      (Eventually.of_forall fun n => ha (pellFamily_ratio_mem n))

/-- **Theorem A (strict least-upper-bound form).** `ρ*` is the least upper
bound, while every individual positive-cost instance lies strictly below it.
@isnad1 id=and.0h0v.s3.187aa5dbe776 from=translated src=- shape=db2cc95c vocab=537e2c7e
-/
theorem theoremA_strict :
    IsLUB hStarRatios rhoStar ∧
      ∀ I : PositiveCostInstance, I.ratio < rhoStar :=
  ⟨hStarRatios_isLUB, PositiveCostInstance.ratio_lt_rhoStar⟩

/-- The optimization definition of the `H*` extremal ratio equals the closed
form `2/(2√2-1)`.
@isnad1 id=eq.0h0v.s2.7085d4ff22b0 from=translated src=- shape=54c8eceb vocab=0f8e7b2f
-/
theorem rhoHStar_eq_rhoStar : rhoHStar = rhoStar := by
  rw [rhoHStar]
  exact hStarRatios_isLUB.csSup_eq
    ⟨(pellFamilyInstance 0).ratio, pellFamily_ratio_mem 0⟩

/-- The supremum is not attained by any positive-cost instance.
@isnad1 id=not.0h0v.s3.2fe12e59acee from=translated src=- shape=eedf340d vocab=d7b11274
-/
theorem rhoStar_not_mem_hStarRatios : rhoStar ∉ hStarRatios := by
  rintro ⟨I, hI⟩
  have hlt := I.ratio_lt_rhoStar
  rw [hI] at hlt
  exact lt_irrefl _ hlt

/-- **Theorem A (exact endpoint form).** The supremum of all positive-cost
ratios is `ρ*`, and no individual instance attains it.
@isnad1 id=and.0h0v.s3.955e6fcb256e from=translated src=- shape=ffdedc68 vocab=121aa3df
-/
theorem theoremA_exact :
    rhoHStar = rhoStar ∧ rhoStar ∉ hStarRatios :=
  ⟨rhoHStar_eq_rhoStar, rhoStar_not_mem_hStarRatios⟩

end

end Goemans
