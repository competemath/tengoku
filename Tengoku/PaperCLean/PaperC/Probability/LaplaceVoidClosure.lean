import Tengoku.PaperCLean.PaperC.Probability.IndependentThinning
import Tengoku.PaperCLean.PaperC.Probability.PoissonLaplaceFunctional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite closure of the auxiliary-thinning Laplace argument

This module joins the two exact finite interfaces used by Section 14:

* independent exponential thinning identifies a void probability with the
  expectation of the original exponential functional;
* Arratia--Goldstein--Gordon controls that void probability by the
  exponential of the thinned Poisson parameter.

The dependency-graph hypothesis is explicit, so later spatial and marked
instantiations can reuse the statement without any new bridge.
-/

namespace PaperC
namespace LaplaceVoidClosure

open scoped BigOperators

open ArratiaGoldsteinGordonInput
open IndependentThinning
open PoissonVoidApproximation
open SpatialThinningFinite

noncomputable section

universe u v

/-- The thinned indicator count is the previously defined thinned count.
@isnad1 id=eq.0h4v.s5.a226aef728e9 from=translated src=- shape=05539339 vocab=e71e57a7
-/
theorem indicatorSum_thinnedIndicator_eq_thinnedCount
    {Ω : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (z : Ω × (ι → Bool)) :
    indicatorSum (thinnedIndicator X) z =
      thinnedCount (fun i ↦ X i z.1) z.2 := by
  classical
  unfold indicatorSum thinnedCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    thinnedIndicator_eq_true_iff]

/-- Zero thinned count is exactly the no-retained-active event.
@isnad1 id=iff.0h4v.s5.209b0baf876e from=translated src=- shape=7b181a55 vocab=08a81f75
-/
theorem indicatorSum_thinnedIndicator_eq_zero_iff
    {Ω : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (z : Ω × (ι → Bool)) :
    indicatorSum (thinnedIndicator X) z = 0 ↔
      NoRetainedActive (fun i ↦ X i z.1) z.2 := by
  rw [indicatorSum_thinnedIndicator_eq_thinnedCount]
  exact thinnedCount_eq_zero_iff _ _

/-- Exact formula for the thinned Poisson parameter.
@isnad1 id=eq.2h5v.s7.88803f2f9e2e from=translated src=- shape=d527125f vocab=d2acf494
-/
theorem poissonParameter_thinnedIndicator
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) :
    poissonParameter
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (thinnedIndicator X) =
      ∑ i, marginal μ X i * q i := by
  unfold poissonParameter
  apply Finset.sum_congr rfl
  intro i hi
  exact marginal_thinnedIndicator μ X q hq0 hq1 i

end

end LaplaceVoidClosure
end PaperC
