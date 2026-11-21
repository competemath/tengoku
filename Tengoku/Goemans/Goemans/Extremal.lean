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

/-- Every individual positive-cost instance has ratio strictly below `ρ*`.-/
theorem ratio_lt_rhoStar (I : PositiveCostInstance) :
    I.ratio < rhoStar := by
  obtain ⟨S, hS, hcost⟩ := I.1.exists_admissible_ucost_lt I.2
  rw [ratio, div_lt_iff₀ I.2]
  exact lt_of_le_of_lt (I.1.optimalUCost_le hS) hcost

theorem ratio_le_rhoStar (I : PositiveCostInstance) :
    I.ratio ≤ rhoStar :=
  I.ratio_lt_rhoStar.le

end PositiveCostInstance

/-- `ρ*` is the least upper bound of all positive-cost ratios on `H*`.-/
theorem hStarRatios_isLUB : IsLUB hStarRatios rhoStar := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨I, rfl⟩
    exact I.ratio_le_rhoStar
  · intro a ha
    exact le_of_tendsto tendsto_pellFamily_ratio
      (Eventually.of_forall fun n => ha (pellFamily_ratio_mem n))

/-- **Theorem A (strict least-upper-bound form).** `ρ*` is the least upper
bound, while every individual positive-cost instance lies strictly below it.-/
theorem theoremA_strict :
    IsLUB hStarRatios rhoStar ∧
      ∀ I : PositiveCostInstance, I.ratio < rhoStar :=
  ⟨hStarRatios_isLUB, PositiveCostInstance.ratio_lt_rhoStar⟩

/-- The optimization definition of the `H*` extremal ratio equals the closed
form `2/(2√2-1)`.-/
theorem rhoHStar_eq_rhoStar : rhoHStar = rhoStar := by
  rw [rhoHStar]
  exact hStarRatios_isLUB.csSup_eq
    ⟨(pellFamilyInstance 0).ratio, pellFamily_ratio_mem 0⟩

/-- The supremum is not attained by any positive-cost instance.-/
theorem rhoStar_not_mem_hStarRatios : rhoStar ∉ hStarRatios := by
  rintro ⟨I, hI⟩
  have hlt := I.ratio_lt_rhoStar
  rw [hI] at hlt
  exact lt_irrefl _ hlt

/-- **Theorem A (exact endpoint form).** The supremum of all positive-cost
ratios is `ρ*`, and no individual instance attains it.-/
theorem theoremA_exact :
    rhoHStar = rhoStar ∧ rhoStar ∉ hStarRatios :=
  ⟨rhoHStar_eq_rhoStar, rhoStar_not_mem_hStarRatios⟩

end

end Goemans
