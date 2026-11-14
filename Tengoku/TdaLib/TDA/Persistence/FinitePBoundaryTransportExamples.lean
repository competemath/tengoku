import Tengoku.TdaLib.TDA.Persistence.FinitePBoundaryTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real-exponent boundary transport examples

These calculations distinguish powered sums from their roots, linear plan masses
from powered distance coefficients, and exponent-dependent matching minimizers.
-/

noncomputable section
namespace TDA.Persistence.FinitePBoundaryTransportExamples
open scoped Classical

/-- Two source points with diagonal charges 1 and 2.-/
def twoDeaths : Fin 2 → ℝ × ℝ := ![(0, 2), (0, 4)]

/-- Two boundary charges 1 and 2 give squared cost 5, before taking the root.
@isnad1 id=eq.0h0v.s5.dccc803962f7 from=translated src=- shape=b0e58762 vocab=1f82cf5b
-/
theorem deletion_power_two :
    finitePowerBoundaryTransportCost 2 twoDeaths (Fin.elim0 : Fin 0 → ℝ × ℝ) = 5 := by
  rw [finitePowerBoundaryTransportCost_of_isEmpty_right, Fin.sum_univ_two]
  norm_num [twoDeaths, diagonalCost, Real.rpow_two]

/-- Root the sum of powers, rather than summing roots.
@isnad1 id=eq.0h0v.s5.b6c756e2e345 from=translated src=- shape=3f143ef3 vocab=adbbf6a3
-/
theorem deletion_root_two :
    finitePBoundaryTransportCost 2 twoDeaths (Fin.elim0 : Fin 0 → ℝ × ℝ) = Real.sqrt 5 := by
  rw [finitePBoundaryTransportCost, deletion_power_two]
  norm_num [Real.sqrt_eq_rpow]

/--
@isnad1 id=eq.0h0v.s5.5cf11f7469e1 from=translated src=- shape=f6db1ee9 vocab=1f82cf5b
-/
theorem insertion_power_two :
    finitePowerBoundaryTransportCost 2 (Fin.elim0 : Fin 0 → ℝ × ℝ) twoDeaths = 5 := by
  rw [finitePowerBoundaryTransportCost_of_isEmpty_left, Fin.sum_univ_two]
  norm_num [twoDeaths, diagonalCost, Real.rpow_two]

/--
@isnad1 id=eq.0h1v.s5.9ae27bfe3057 from=translated src=- shape=56ae6a8d vocab=b520761b
-/
theorem empty_power (p : ℝ) :
    finitePowerBoundaryTransportCost p (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 := by simp

/--
@isnad1 id=eq.1h1v.s5.2a59b09d3d27 from=translated src=- shape=5679cc2c vocab=ca9f054b
-/
theorem empty_root {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 := finitePBoundaryTransportCost_empty hp _ _

/-- A genuinely fractional real plan, with a half unit left at each boundary.-/
def halfPlan : FiniteBoundaryPlan (Fin 1) (Fin 1) where
  mass _ _ := 1 / 2
  nonneg _ _ := by norm_num
  row_le_one _ := by norm_num
  col_le_one _ := by norm_num

/--
@isnad1 id=and.0h0v.s8.d0dbbfc845c2 from=translated src=- shape=897ad2fb vocab=21c7b8c7
-/
theorem half_plan_cost_and_deficits :
    halfPlan.mass 0 0 = 1 / 2 ∧ halfPlan.deletionMass 0 = 1 / 2 ∧
    halfPlan.insertionMass 0 = 1 / 2 ∧
    halfPlan.powerCost 2 (fun _ => (0, 2)) (fun _ => (0, 4)) = 9 / 2 := by
  norm_num [halfPlan, FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass,
    FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost, finitePairCost, diagonalCost,
    Real.rpow_two]

/-- The singleton minimum really compares powered pairing and deleting-both costs.
@isnad1 id=eq.0h0v.s6.023707bf398a from=translated src=- shape=524160f5 vocab=3394ee69
-/
theorem paired_power_two :
    finitePowerBoundaryTransportCost 2 (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
      (fun _ : Fin 1 => (0, 4)) = 4 := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_singleton]
  norm_num [finitePairCost, diagonalCost, Real.rpow_two]

/--
@isnad1 id=eq.0h0v.s7.0c94a8c4b4b3 from=translated src=- shape=8f1692de vocab=2e1992ca
-/
theorem switch_power_one :
    finitePowerBoundaryTransportCost 1 (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
      (fun _ : Fin 1 => (3 / 2, 7 / 2)) = 3 / 2 := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_singleton]
  norm_num [finitePairCost, diagonalCost]

/--
@isnad1 id=eq.0h0v.s6.5aafbeef6fec from=translated src=- shape=a139aa49 vocab=2e1992ca
-/
theorem switch_power_two :
    finitePowerBoundaryTransportCost 2 (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
      (fun _ : Fin 1 => (3 / 2, 7 / 2)) = 2 := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_singleton]
  norm_num [finitePairCost, diagonalCost, Real.rpow_two]

def pairSingletons : OccurrenceMatching (Fin 1) (Fin 1) PEmpty.{1} PEmpty.{1} where
  finite i := some i
  finite_injective _ _ _ _ _ := Subsingleton.elim _ _
  essential := Equiv.refl _

/-- The p=1 optimizer is strictly suboptimal for p=2.
@isnad1 id=and.0h0v.s8.6a8512b0f74b from=translated src=- shape=6b1d5cd7 vocab=3b1a82d8
-/
theorem optimizer_changes_with_exponent :
    pairSingletons.totalFinitePowerCost 1 (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2)) =
        finitePowerBoundaryTransportCost 1 (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
          (fun _ : Fin 1 => (3 / 2, 7 / 2)) ∧
    finitePowerBoundaryTransportCost 2 (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
        (fun _ : Fin 1 => (3 / 2, 7 / 2)) <
      pairSingletons.totalFinitePowerCost 2 (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2)) := by
  rw [switch_power_one, switch_power_two]
  norm_num [pairSingletons, OccurrenceMatching.totalFinitePowerCost,
    OccurrenceMatching.totalBoundaryCost, finitePairCost, diagonalCost, Real.rpow_two]

/--
@isnad1 id=eq.0h0v.s8.37bc801518c1 from=translated src=- shape=c8f3526c vocab=593f8b18
-/
theorem deleting_both_optimal_at_two :
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan (Fin 1) (Fin 1)).powerCost 2
        (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2)) =
      finitePowerBoundaryTransportCost 2 (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
        (fun _ : Fin 1 => (3 / 2, 7 / 2)) := by
  rw [switch_power_two]
  norm_num [FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost,
    FiniteBoundaryPlan.zero, FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass,
    finitePairCost, diagonalCost, Real.rpow_two]

/-- Optimizing must be repeated after changing the exponent.
@isnad1 id=ne.0h0v.s7.a43f77cd1c3e from=translated src=- shape=7aa06e4b vocab=c30e0674
-/
theorem powered_optimum_not_power_of_first_order :
    finitePowerBoundaryTransportCost 2 (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
        (fun _ : Fin 1 => (3 / 2, 7 / 2)) ≠
      (finiteFirstOrderBoundaryTransportCost (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
        (fun _ : Fin 1 => (3 / 2, 7 / 2))) ^ 2 := by
  rw [switch_power_two, ← finitePowerBoundaryTransportCost_one, switch_power_one]
  norm_num

/-- Split two distinct source occurrences between one target occurrence.-/
def repeatedHalfPlan : FiniteBoundaryPlan (Fin 2) Unit where
  mass _ _ := 1 / 2
  nonneg _ _ := by norm_num
  row_le_one _ := by norm_num
  col_le_one _ := by norm_num [Fin.sum_univ_two]

/--
@isnad1 id=eq.0h0v.s6.b7f41d6a0a7d from=translated src=- shape=01767ae0 vocab=196d495f
-/
theorem repeated_fractional_cost :
    repeatedHalfPlan.powerCost 2 (fun _ => (0, 2)) (fun _ => (0, 2)) = 1 := by
  norm_num [FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost,
    FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass, repeatedHalfPlan,
    Fin.sum_univ_two, finitePairCost, diagonalCost, Real.rpow_two]

/-- Retaining multiplicity forces one deletion even though all coordinate values coincide.
@isnad1 id=eq.0h0v.s6.68d741af8b34 from=translated src=- shape=4f3839c9 vocab=f325e2d1
-/
theorem repeated_minimum :
    finitePowerBoundaryTransportCost 2 (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (0, 2)) = 1 := by
  apply le_antisymm
  · exact (finitePowerBoundaryTransportCost_le_plan _ _ _ repeatedHalfPlan).trans_eq
      repeated_fractional_cost
  · rw [finitePowerBoundaryTransportCost_eq_matchingCost]
    apply (le_finitePowerMatchingCost_iff _ _ _ _).mpr
    intro M
    cases h0 : M.finite 0 with
    | none =>
      cases h1 : M.finite 1 with
      | none =>
        norm_num [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost,
          Fin.sum_univ_two, Fin.exists_fin_succ, h0, h1, diagonalCost, Real.rpow_two]
        simp
      | some j =>
        cases j
        norm_num [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost,
          Fin.sum_univ_two, Fin.exists_fin_succ, h0, h1, finitePairCost, diagonalCost, Real.rpow_two]
    | some j =>
      cases j
      cases h1 : M.finite 1 with
      | none =>
        norm_num [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost,
          Fin.sum_univ_two, Fin.exists_fin_succ, h0, h1, finitePairCost, diagonalCost, Real.rpow_two]
      | some j =>
        cases j
        have h := M.finite_injective 0 1 () h0 h1
        norm_num at h

/--
@isnad1 id=eq.0h0v.s6.4545cf51d9b3 from=translated src=- shape=4f3839c9 vocab=ba65cbc1
-/
theorem repeated_root :
    finitePBoundaryTransportCost 2 (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (0, 2)) = 1 := by
  rw [finitePBoundaryTransportCost, repeated_minimum]
  simp

/-- Fractional and incidence optima coexist; every optimum need not be integral.
@isnad1 id=and.0h0v.s7.45787fa0af3b from=translated src=- shape=29b8ce0e vocab=2febe48a
-/
theorem fractional_and_integral_optima :
    repeatedHalfPlan.powerCost 2 (fun _ => (0, 2)) (fun _ => (0, 2)) =
        finitePowerBoundaryTransportCost 2 (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
          (fun _ : Unit => (0, 2)) ∧
    ∃ M : OccurrenceMatching (Fin 2) Unit PEmpty.{1} PEmpty.{1},
      (FiniteBoundaryPlan.ofMatching M).powerCost 2 (fun _ => (0, 2)) (fun _ => (0, 2)) = 1 := by
  refine ⟨by rw [repeated_minimum, repeated_fractional_cost], ?_⟩
  simpa only [repeated_minimum] using exists_minimizing_powerBoundaryPlan 2
    (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ)) (fun _ : Unit => (0, 2))

/-- A noninteger exponent uses the same real-power API, not integer powers.
@isnad1 id=eq.0h0v.s6.d998d6f339b1 from=translated src=- shape=0f6497b6 vocab=a8898f54
-/
theorem noninteger_power :
    finitePowerBoundaryTransportCost (3 / 2) (fun _ : Fin 1 => ((0, 8) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 8 := by
  rw [finitePowerBoundaryTransportCost_of_isEmpty_right]
  norm_num [diagonalCost]

/--
@isnad1 id=eq.0h0v.s6.2ef60d6a4a03 from=translated src=- shape=0f6497b6 vocab=4bf81e2d
-/
theorem noninteger_root :
    finitePBoundaryTransportCost (3 / 2) (fun _ : Fin 1 => ((0, 8) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 4 := by
  rw [finitePBoundaryTransportCost, noninteger_power]
  rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 3 (((3 : ℝ) / 2)⁻¹)]
  norm_num [Real.rpow_natCast]

/-- Unequal diagonal charges survive a nontrivial source relabelling.
@isnad1 id=eq.0h0v.s7.a02dbac488d9 from=translated src=- shape=930423b1 vocab=7ceb6cf0
-/
theorem relabelled_power :
    finitePowerBoundaryTransportCost 2 (twoDeaths ∘ Equiv.swap 0 1)
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 5 := by
  have h := finitePowerBoundaryTransportCost_reindex
    (Equiv.swap 0 1) (Equiv.refl (Fin 0)) 2 twoDeaths (Fin.elim0 : Fin 0 → ℝ × ℝ)
  simpa only [Function.comp_id, Equiv.coe_refl, deletion_power_two] using h

/-- Squared optima themselves fail the ordinary triangle inequality.
@isnad1 id=lt.0h0v.s8.23433db022bd from=translated src=- shape=afdbdc7a vocab=bd74f29c
-/
theorem powered_cost_not_metric :
    finitePowerBoundaryTransportCost 2 (fun _ : Fin 1 => ((0, 10) : ℝ × ℝ))
        (fun _ : Fin 1 => (1, 11)) +
      finitePowerBoundaryTransportCost 2 (fun _ : Fin 1 => ((1, 11) : ℝ × ℝ))
        (fun _ : Fin 1 => (2, 12)) <
      finitePowerBoundaryTransportCost 2 (fun _ : Fin 1 => ((0, 10) : ℝ × ℝ))
        (fun _ : Fin 1 => (2, 12)) := by
  simp only [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_singleton]
  norm_num [finitePairCost, diagonalCost, Real.rpow_two]

end TDA.Persistence.FinitePBoundaryTransportExamples
