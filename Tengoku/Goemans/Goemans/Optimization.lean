/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.Admissibility
import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The exact optimization problem on `H*`

There are only eight unsplittable routings on the three-terminal graph.  This
file packages the minimum over the admissible routings and the corresponding
set of positive-cost approximation ratios.  The definitions are
noncomputable only because they select a minimum and a supremum; their
underlying sets are finite or explicitly defined ranges.
-/

namespace Goemans

noncomputable section

namespace FlowInstance

/-- The finite set of routings satisfying the Dinitz--Garg--Goemans capacity
bound.-/
def admissibleRoutings (I : FlowInstance ℝ) : Finset (Finset Terminal) :=
  Finset.univ.filter I.Admissible

theorem mem_admissibleRoutings (I : FlowInstance ℝ) (S : Finset Terminal) :
    S ∈ I.admissibleRoutings ↔ I.Admissible S := by
  simp [admissibleRoutings]

theorem admissibleRoutings_nonempty (I : FlowInstance ℝ) :
    I.admissibleRoutings.Nonempty :=
  ⟨∅, I.mem_admissibleRoutings ∅ |>.2 I.admissible_empty⟩

/-- The finite set of costs of admissible routings.-/
private def admissibleCosts (I : FlowInstance ℝ) : Finset ℝ :=
  I.admissibleRoutings.image I.ucost

private theorem admissibleCosts_nonempty (I : FlowInstance ℝ) :
    I.admissibleCosts.Nonempty :=
  I.admissibleRoutings_nonempty.image I.ucost

/-- Minimum cost among all admissible unsplittable routings.-/
def optimalUCost (I : FlowInstance ℝ) : ℝ :=
  I.admissibleCosts.min' I.admissibleCosts_nonempty

/-- An optimal admissible routing exists.-/
theorem exists_optimalRouting (I : FlowInstance ℝ) :
    ∃ S : Finset Terminal, I.Admissible S ∧ I.ucost S = I.optimalUCost := by
  have hmem :
      I.optimalUCost ∈ I.admissibleCosts :=
    Finset.min'_mem _ I.admissibleCosts_nonempty
  rcases Finset.mem_image.mp hmem with ⟨S, hS, hcost⟩
  exact ⟨S, I.mem_admissibleRoutings S |>.1 hS, hcost⟩

/-- The optimum is no larger than the cost of any admissible routing.-/
theorem optimalUCost_le (I : FlowInstance ℝ) {S : Finset Terminal}
    (hS : I.Admissible S) :
    I.optimalUCost ≤ I.ucost S := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨S, I.mem_admissibleRoutings S |>.2 hS, rfl⟩

/-- A common lower bound for all admissible routing costs bounds the optimum.-/
theorem le_optimalUCost (I : FlowInstance ℝ) {r : ℝ}
    (h : ∀ S : Finset Terminal, I.Admissible S → r ≤ I.ucost S) :
    r ≤ I.optimalUCost := by
  obtain ⟨S, hS, hcost⟩ := I.exists_optimalRouting
  rw [← hcost]
  exact h S hS

/-- The minimum admissible unsplittable-routing cost is nonnegative.-/
theorem optimalUCost_nonneg (I : FlowInstance ℝ) :
    0 ≤ I.optimalUCost :=
  I.le_optimalUCost fun S _ => I.ucost_nonneg S

end FlowInstance

/-- A real-valued flow instance whose fractional cost is positive.-/
abbrev PositiveCostInstance := {I : FlowInstance ℝ // 0 < I.fcost}

namespace PositiveCostInstance

/-- The exact optimum-to-fractional-cost ratio of a positive-cost instance.-/
def ratio (I : PositiveCostInstance) : ℝ :=
  I.1.optimalUCost / I.1.fcost

end PositiveCostInstance

/-- The set of all positive-cost ratios on the Rybin graph `H*`.-/
def hStarRatios : Set ℝ := Set.range PositiveCostInstance.ratio

/-- The extremal ratio of `H*`, defined as the supremum of all
positive-fractional-cost instance ratios.-/
def rhoHStar : ℝ := sSup hStarRatios

end

end Goemans
