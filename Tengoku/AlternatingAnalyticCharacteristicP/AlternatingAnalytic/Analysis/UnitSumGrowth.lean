import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.EquivalentUltrametric
import Tengoku.Seed.Analysis.Normed.Operator.LinearIsometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linear growth of unit sums

A normed group has linear unit-sum growth if some vectors of norm at most one have partial sums
of norm at least `N / M`. This rules out an equivalent ultrametric norm over any scalar field.
It is used in Proposition E.1.
-/

namespace AlternatingAnalytic

/-- There are vectors of norm at most one whose partial sums grow linearly. The property
involves only the additive norm, not a scalar field.-/
def HasLinearUnitSumGrowth (F : Type*) [NormedAddCommGroup F] : Prop :=
  ∃ (v : ℕ → F) (M : ℝ), 0 < M ∧ (∀ j, ‖v j‖ ≤ 1) ∧
    ∀ N : ℕ, (N : ℝ) / M ≤ ‖∑ i ∈ Finset.range N, v i‖

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Linear unit-sum growth passes along additive isometries.-/
theorem HasLinearUnitSumGrowth.map (h : HasLinearUnitSumGrowth E)
    (i : E →+ F) (hi : Isometry i) : HasLinearUnitSumGrowth F := by
  obtain ⟨v, M, hM, hv, hgrowth⟩ := h
  have hn (x : E) : ‖i x‖ = ‖x‖ := hi.norm_map_of_map_zero i.map_zero x
  refine ⟨i ∘ v, M, hM, fun j => ?_, fun N => ?_⟩
  · simpa only [Function.comp_apply, hn] using hv j
  · simpa only [Function.comp_apply, ← map_sum, hn] using hgrowth N

/-- A space with linear unit-sum growth has no equivalent ultrametric norm, over any
scalar field.-/
theorem HasLinearUnitSumGrowth.not_hasEquivalentUltrametricNorm
    (h : HasLinearUnitSumGrowth F) (K : Type*) [NormedField K] [NormedSpace K F] :
    ¬ HasEquivalentUltrametricNorm K F := by
  obtain ⟨v, M, hM, hv, hgrowth⟩ := h
  exact not_hasEquivalentUltrametricNorm_of_linear_growth v hv hM hgrowth

end AlternatingAnalytic
