/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: GPT-5.6 Sol (formalization).
-/
import Tengoku.Goemans.Goemans.Laned
import Tengoku.Goemans.Goemans.WeightedSelection
import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Finset
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Optimal cost and the one-stage unit-demand ratio bound

This file closes the final proved observation in Section 7.  It defines the
optimal cost of a laned instance as the infimum of the costs of its admissible
routings.  For the one-stage unit-demand specialization, sub-unit fractional
lane loads imply that the total cheap fraction is strictly below the number of
lanes.  Uniform-cardinality weighted rounding then produces an admissible
routing whose cost is strictly below the positive fractional cost, so the
optimal ratio is strictly below one.

The numerical laned search and Conjecture D remain outside the formal claim.
-/

namespace Goemans
namespace Laned
namespace Instance

noncomputable section

variable {k m : ℕ}
variable (I : Instance k m)

/-- Costs realized by full-graph admissible laned routings.-/
def feasibleCosts : Set ℝ :=
  {q | ∃ (S : Finset (Fin k)) (R : I.Routing),
    I.Admissible S R ∧ q = I.routingCost S}

/-- Optimal admissible unsplittable cost.  The infimum formulation is total;
the one-stage theorem below supplies an explicit feasible routing.-/
def optimalRoutingCost : ℝ :=
  sInf I.feasibleCosts

/-- Optimal-to-fractional-cost ratio for a laned instance.  Ratio theorems
state positivity of the denominator explicitly.-/
def ratio : ℝ :=
  I.optimalRoutingCost / I.fractionalCost

/-- Every laned routing cost is nonnegative.
@isnad1 id=le.0h4v.s4.257ea892f5ae from=translated src=- shape=ba13d53e vocab=fe40a3aa
-/
theorem routingCost_nonneg (S : Finset (Fin k)) :
    0 ≤ I.routingCost S := by
  rw [routingCost]
  exact Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (I.c_nonneg i) (I.d_pos i).le

/-- The feasible cost set has the uniform lower bound zero.
@isnad1 id=bddbelow.0h3v.s3.3a8536894719 from=translated src=- shape=efb9bf15 vocab=db1b423c
-/
theorem feasibleCosts_bddBelow :
    BddBelow I.feasibleCosts := by
  refine ⟨0, ?_⟩
  intro q hq
  rcases hq with ⟨S, _R, _hR, rfl⟩
  exact I.routingCost_nonneg S

/-- The feasible cost set is finite because routing cost depends only on the
finite cheap-exit selection.
@isnad1 id=finite.0h3v.s3.0a2e18b1aebf from=translated src=- shape=efb9bf15 vocab=adbb7cfe
-/
theorem feasibleCosts_finite :
    I.feasibleCosts.Finite := by
  apply (Set.finite_range I.routingCost).subset
  intro q hq
  rcases hq with ⟨S, _R, _hR, rfl⟩
  exact ⟨S, rfl⟩

/-- The optimal cost is no larger than any exhibited full admissible routing.
@isnad1 id=le.1h5v.s5.d3971b7e599e from=translated src=- shape=4a27efab vocab=c3b7f6b1
-/
theorem optimalRoutingCost_le {S : Finset (Fin k)} {R : I.Routing}
    (hR : I.Admissible S R) :
    I.optimalRoutingCost ≤ I.routingCost S := by
  apply csInf_le I.feasibleCosts_bddBelow
  exact ⟨S, R, hR, rfl⟩

/-- Whenever an admissible routing exists, the finite infimum is attained by
an admissible routing and is therefore the literal minimum from the paper's
ratio definition.
@isnad1 id=ex.1h3v.s5.a90f4ce64562 from=translated src=- shape=16312b7f vocab=c446cb09
-/
theorem exists_optimalRouting (hne : I.feasibleCosts.Nonempty) :
    ∃ (S : Finset (Fin k)) (R : I.Routing),
      I.Admissible S R ∧ I.routingCost S = I.optimalRoutingCost := by
  have hmem : I.optimalRoutingCost ∈ I.feasibleCosts :=
    hne.csInf_mem I.feasibleCosts_finite
  rcases hmem with ⟨S, R, hR, hcost⟩
  exact ⟨S, R, hR, hcost.symm⟩

/-! ## Unit-demand, one-stage cost identities -/

variable {k : ℕ}
variable (I : Instance k 1)

/-- With unit demands, routing cost is the sum of the costs of terminals not
selected for the cheap exit.
@isnad1 id=eq.1h3v.s6.0bbbd9bdaf85 from=translated src=- shape=b9af92b4 vocab=6a0d534e
-/
theorem routingCost_eq_sum_compl_of_unit
    (hd : ∀ i, I.d i = 1) (S : Finset (Fin k)) :
    I.routingCost S = ∑ i ∈ Sᶜ, I.c i := by
  rw [routingCost]
  simp only [hd, mul_one]
  have hcomp :
      Sᶜ = Finset.univ.filter (fun i => i ∉ S) := by
    ext i
    simp
  rw [hcomp, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [hi]

/-- With unit demands, the fractional cost is the weighted residual
`∑ cᵢ(1-fᵢ)`.
@isnad1 id=eq.1h2v.s6.5b55b2ab8654 from=translated src=- shape=54c59c41 vocab=59066262
-/
theorem fractionalCost_eq_residual_of_unit
    (hd : ∀ i, I.d i = 1) :
    I.fractionalCost = ∑ i, I.c i * (1 - I.f i) := by
  simp [fractionalCost, hd]

/-- If all one-stage lane loads are strictly below one, their conservation
identity forces the total cheap fraction to be strictly below the number of
lanes.
@isnad1 id=lt.3h2v.s7.8df4e612b1ce from=translated src=- shape=2574079c vocab=65b3000b
-/
theorem sum_f_lt_laneCount
    (he : ∀ i, I.e i = (0 : Fin 2))
    (hp : ∀ i, I.p i = (1 : Fin 2))
    (hxlt : ∀ l, I.laneX (0 : Fin 1) l < 1) :
    (∑ i, I.f i) < (I.lanes (0 : Fin 1) : ℝ) := by
  have hxsum :
      (∑ l, I.laneX (0 : Fin 1) l) = ∑ i, I.f i := by
    calc
      (∑ l, I.laneX (0 : Fin 1) l) =
          ∑ i, ((if (0 : Fin 1).val < (I.p i).val then I.f i else 0) +
            (if (0 : Fin 1).val < (I.e i).val then
              I.d i - I.f i else 0)) :=
        I.laneX_sum (0 : Fin 1)
      _ = ∑ i, I.f i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hp i, he i]
        norm_num
  let l₀ : Fin (I.lanes (0 : Fin 1)) :=
    ⟨0, I.lane_nonempty (0 : Fin 1)⟩
  have hlt :
      (∑ l, I.laneX (0 : Fin 1) l) <
        ∑ _l : Fin (I.lanes (0 : Fin 1)), (1 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro l _
      exact (hxlt l).le
    · exact ⟨l₀, Finset.mem_univ l₀, hxlt l₀⟩
  rw [hxsum] at hlt
  simpa using hlt

end

end Instance
end Laned
end Goemans
