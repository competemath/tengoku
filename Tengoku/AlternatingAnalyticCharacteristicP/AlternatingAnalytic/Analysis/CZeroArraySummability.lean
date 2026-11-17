import Tengoku.Seed.Topology.ContinuousMap.ZeroAtInfty
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Nonarchimedean
import Tengoku.Seed.Analysis.Normed.Group.Ultra
import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Summability of bounded coefficient arrays on c₀

For `x r ∈ C₀(I, K)` with `I` discrete, the products `∏ r, x r (a r)` tend to zero
along the cofinite filter on tuples `a`. Hence, for a bounded array `c` with values in
a complete ultrametric space, `∑ a, (∏ r, x r (a r)) • c a` is unconditionally summable.
-/

open scoped Topology ZeroAtInfty BigOperators
open Filter

namespace CZero

variable {I K W : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NontriviallyNormedField K]

/-- A discrete c₀ vector tends to zero on the cofinite filter.-/
theorem tendsto_cofinite_of_zeroAtInfty (x : C₀(I, K)) : Tendsto x cofinite (𝓝 0) := by
  simpa only [Filter.cocompact_eq_cofinite] using zero_at_infty x

/-- The products `∏ r, x r (a r)` tend to zero along the cofinite filter on tuples `a`.-/
theorem tendsto_coordinate_prod (n : ℕ) (x : Fin n → C₀(I, K)) :
    Tendsto (fun a : Fin n → I => ∏ r, x r (a r)) cofinite (𝓝 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi : Function.Injective
        (fun a : Fin (n + 1) → I => (a 0, fun r : Fin n => a r.succ)) := by
      intro a b h
      funext r
      refine Fin.cases ?_ (fun j => ?_) r
      · exact congrArg Prod.fst h
      · exact congrFun (congrArg Prod.snd h) j
    have h := (tendsto_mul_cofinite_nhds_zero (tendsto_cofinite_of_zeroAtInfty (x 0))
      (ih (fun r => x r.succ))).comp hi.tendsto_cofinite
    simpa only [Function.comp_def, Fin.prod_univ_succ] using h

variable [NormedAddCommGroup W] [NormedSpace K W]

/-- For a bounded array `c`, the terms `(∏ r, x r (a r)) • c a` tend to zero cofinitely.-/
theorem tendsto_arraySummand_cofinite_zero {n : ℕ}
    (c : (Fin n → I) → W) (C : ℝ) (_hC : 0 ≤ C) (hc : ∀ a, ‖c a‖ ≤ C)
    (x : Fin n → C₀(I, K)) :
    Tendsto (fun a => (∏ r, x r (a r)) • c a) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hp := (tendsto_coordinate_prod n x).norm
  simp only [norm_zero] at hp
  have h := bdd_le_mul_tendsto_zero' (f := fun a => ‖c a‖) C
    (Filter.Eventually.of_forall (fun a => by simpa only [abs_norm] using hc a)) hp
  simpa only [norm_smul, mul_comm] using h

/-- For a bounded array with values in a complete ultrametric space, the family
`(∏ r, x r (a r)) • c a` is summable.-/
theorem summable_arraySummand [IsUltrametricDist W] [CompleteSpace W]
    {n : ℕ} (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin n → C₀(I, K)) :
    Summable (fun a => (∏ r, x r (a r)) • c a) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_arraySummand_cofinite_zero c C hC hc x)

end CZero
