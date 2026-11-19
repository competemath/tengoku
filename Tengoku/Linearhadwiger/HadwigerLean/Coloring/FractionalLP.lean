import Tengoku.Linearhadwiger.HadwigerLean.Coloring.Fractional
import Tengoku.Linearhadwiger.HadwigerLean.Optimization.FiniteLP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fractional coloring as a finite covering linear program

The rows are vertices and the columns are nonempty stable sets.  This module
identifies both feasible regions and both objective functions with the generic
finite LP interface.
-/

namespace HadwigerLean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The covering LP for fractional chromatic number.-/
noncomputable def fractionalLP (G : SimpleGraph V) :
    FiniteLP.Problem V (StableSet G) where
  A v S := if v ∈ S.1 then 1 else 0
  b _ := 1
  c _ := 1

/--
@isnad1 id=iff.0h3v.s5.8994d8165c83 from=translated src=- shape=0b9e7129 vocab=7c652140
-/
theorem fractionalLP_primalFeasible_iff (G : SimpleGraph V)
    (x : StableSet G → ℝ) :
    (fractionalLP G).PrimalFeasible x ↔ IsFractionalColoring G x := by
  classical
  simp only [FiniteLP.Problem.PrimalFeasible, IsFractionalColoring,
    fractionalLP, vertexLoad]
  constructor <;> rintro ⟨hnonneg, hcover⟩ <;> refine ⟨hnonneg, ?_⟩
  · intro v
    simpa [ite_mul] using hcover v
  · intro v
    simpa [ite_mul] using hcover v

/--
@isnad1 id=iff.0h3v.s4.ad47ae6928ee from=translated src=- shape=d9af210f vocab=d3d92d27
-/
theorem fractionalLP_dualFeasible_iff (G : SimpleGraph V) (w : V → ℝ) :
    (fractionalLP G).DualFeasible w ↔ IsFractionalDualFeasible G w := by
  classical
  simp only [FiniteLP.Problem.DualFeasible, IsFractionalDualFeasible,
    fractionalLP]
  constructor <;> rintro ⟨hnonneg, hstable⟩ <;> refine ⟨hnonneg, ?_⟩
  · intro S
    simpa [ite_mul, Finset.sum_ite] using hstable S
  · intro S
    simpa [ite_mul, Finset.sum_ite] using hstable S

/--
@isnad1 id=eq.0h3v.s5.f905ca4b7fd9 from=translated src=- shape=21a573e3 vocab=a1211611
-/
theorem fractionalLP_primalValue (G : SimpleGraph V) (x : StableSet G → ℝ) :
    (fractionalLP G).primalValue x = fractionalCost G x := by
  simp [FiniteLP.Problem.primalValue, fractionalLP, fractionalCost]

/--
@isnad1 id=eq.0h3v.s5.bd1294761926 from=translated src=- shape=bb55b18c vocab=df429b37
-/
theorem fractionalLP_dualValue (G : SimpleGraph V) (w : V → ℝ) :
    (fractionalLP G).dualValue w = fractionalDualValue w := by
  simp [FiniteLP.Problem.dualValue, fractionalLP, fractionalDualValue]

/-- On a finite graph, the infimum defining fractional chromatic number is attained.
@isnad1 id=ex.0h2v.s5.85d606c73b22 from=translated src=- shape=90ac94e7 vocab=9f037fa3
-/
theorem exists_fractionalColoring_minimizer (G : SimpleGraph V) :
    ∃ x : StableSet G → ℝ,
      IsFractionalColoring G x ∧
        fractionalCost G x = fractionalChromaticNumber G := by
  classical
  have hc : ∀ S : StableSet G, 0 < (fractionalLP G).c S := by
    intro S
    simp [fractionalLP]
  have hsingle : (fractionalLP G).PrimalFeasible
      (singletonFractionalColoring G) :=
    (fractionalLP_primalFeasible_iff G _).2
      (singletonFractionalColoring_feasible G)
  obtain ⟨x, hx, hmin⟩ :=
    (fractionalLP G).exists_primal_minimizer hc hsingle
  have hx' : IsFractionalColoring G x :=
    (fractionalLP_primalFeasible_iff G x).1 hx
  refine ⟨x, hx', le_antisymm ?_ (fractionalChromaticNumber_le_cost G hx')⟩
  unfold fractionalChromaticNumber
  apply le_csInf
  · exact ⟨fractionalCost G x, x, hx', rfl⟩
  · rintro t ⟨z, hz, rfl⟩
    simpa only [fractionalLP_primalValue] using
      hmin z ((fractionalLP_primalFeasible_iff G z).2 hz)

/-- Fractional coloring has optimal primal and dual solutions with equal values.
@isnad1 id=ex.0h2v.s6.002e1aee45f3 from=translated src=- shape=06eb75ca vocab=dc41fb75
-/
theorem exists_fractional_primal_dual_optima (G : SimpleGraph V) :
    ∃ x : StableSet G → ℝ, ∃ w : V → ℝ,
      IsFractionalColoring G x ∧ IsFractionalDualFeasible G w ∧
        fractionalCost G x = fractionalDualValue w ∧
        fractionalChromaticNumber G = fractionalCost G x := by
  classical
  have hc : ∀ S : StableSet G, 0 < (fractionalLP G).c S := by
    intro S
    simp [fractionalLP]
  have hsingle : (fractionalLP G).PrimalFeasible
      (singletonFractionalColoring G) :=
    (fractionalLP_primalFeasible_iff G _).2
      (singletonFractionalColoring_feasible G)
  obtain ⟨x, w, hx, hw, heq⟩ :=
    (fractionalLP G).exists_primal_dual_optima hc hsingle
  have hx' : IsFractionalColoring G x :=
    (fractionalLP_primalFeasible_iff G x).1 hx
  have hw' : IsFractionalDualFeasible G w :=
    (fractionalLP_dualFeasible_iff G w).1 hw
  have hcost : fractionalCost G x = fractionalDualValue w := by
    simpa only [fractionalLP_primalValue, fractionalLP_dualValue] using heq
  refine ⟨x, w, hx', hw', hcost, ?_⟩
  apply le_antisymm (fractionalChromaticNumber_le_cost G hx')
  calc
    fractionalCost G x = fractionalDualValue w := hcost
    _ ≤ fractionalChromaticNumber G := fractionalDualValue_le_chromatic G hw'

/-- The dual vertex-weight formulation attains fractional chromatic number.
@isnad1 id=ex.0h2v.s5.e6762360491a from=translated src=- shape=529ec75e vocab=9bfda4ff
-/
theorem exists_fractionalDual_optimum (G : SimpleGraph V) :
    ∃ w : V → ℝ,
      IsFractionalDualFeasible G w ∧
        fractionalDualValue w = fractionalChromaticNumber G := by
  obtain ⟨x, w, _, hw, hcost, hchrom⟩ :=
    exists_fractional_primal_dual_optima G
  exact ⟨w, hw, hcost.symm.trans hchrom.symm⟩

/--
@isnad1 id=eq.0h2v.s4.fcabfbfef04f from=translated src=- shape=d85dc8f5 vocab=6cadbb7d
-/
@[simp] theorem fractionalChromaticNumber_eq_zero_of_isEmpty
    (G : SimpleGraph V) [IsEmpty V] : fractionalChromaticNumber G = 0 := by
  obtain ⟨w, _, hw⟩ := exists_fractionalDual_optimum G
  simpa [fractionalDualValue] using hw.symm

end HadwigerLean
