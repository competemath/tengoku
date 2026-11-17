import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.CZeroArrayAlgebra
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.CZeroArraySummability
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.CZeroCoordinateBasics
import Tengoku.Seed.Data.Fintype.Pi
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded coefficient arrays on discrete c₀

A bounded array `c : (Fin n → I) → W` with values in a complete ultrametric
space defines a continuous `n`-linear map on `C₀(I, K)` (supremum norm) by
`x ↦ ∑' a, (∏ r, x r (a r)) • c a`, of norm at most the bound on `c`. This is
the coefficient lifting step in the proof of Theorem 4.5(1).
-/

noncomputable section

open scoped Topology ZeroAtInfty BigOperators
open Filter

namespace CZero

variable {I K W : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NontriviallyNormedField K] [NormedAddCommGroup W] [NormedSpace K W] {n : ℕ}

omit [DiscreteTopology I] in
/-- On inputs supported in finite coordinate sets, the array sum is a finite sum.
@isnad1 id=eq.1h7v.s9.b6679e7fa34e from=translated src=- shape=d153be5e vocab=e5644e99
-/
theorem array_tsum_eq_sum (c : (Fin n → I) → W) (x : Fin n → C₀(I, K))
    (s : Fin n → Finset I) (hx : ∀ r i, i ∉ s r → x r i = 0) :
    (∑' a : Fin n → I, (∏ r, x r (a r)) • c a) =
      ∑ a ∈ Fintype.piFinset s, (∏ r, x r (a r)) • c a := by
  classical
  apply tsum_eq_sum
  intro a ha
  have ha' : ¬ ∀ r, a r ∈ s r := by
    simpa only [Fintype.mem_piFinset] using ha
  obtain ⟨r, hr⟩ := not_forall.mp ha'
  have hz : (∏ j, x j (a j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ r) (hx r (a r) hr)
  rw [hz, zero_smul]

variable [IsUltrametricDist W] [CompleteSpace W]

/-- The unconditional bounded-array sum is multilinear.-/
def boundedArrayMultilinear (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) : MultilinearMap K (fun _ : Fin n => C₀(I, K)) W where
  toFun x := ∑' a, arraySummand c a x
  map_update_add' x r y z := by
    simp only [MultilinearMap.map_update_add]
    exact (summable_arraySummand c C hC hc (Function.update x r y)).tsum_add
      (summable_arraySummand c C hC hc (Function.update x r z))
  map_update_smul' x r b y := by
    simp only [MultilinearMap.map_update_smul]
    exact (summable_arraySummand c C hC hc (Function.update x r y)).tsum_const_smul b

/--
@isnad1 id=eq.2h7v.s9.86b72085d9e6 from=translated src=- shape=06d5ba60 vocab=fcdeea7e
-/
@[simp]
theorem boundedArrayMultilinear_apply (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin n → C₀(I, K)) :
    boundedArrayMultilinear c C hC hc x = ∑' a, (∏ r, x r (a r)) • c a := rfl

end CZero
