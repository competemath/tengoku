/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpKernel
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpExponents
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local `L^{3/2}` bounds for Newtonian potentials of compactly supported data

The Newtonian representation `ext:newtonian` of the paper writes the local pressure as a sum of
Newtonian potentials `N * g` and first-derivative potentials `∂ⱼN * g` of compactly supported
data `g`.  The Liouville step needs each of these to be `L^{3/2}` on every ball of
three-dimensional space.

This file supplies the *near-field* half of that statement: Young's inequality on a ball, with
the kernel truncated at the radius `R + ρ` beyond which it cannot be seen by data supported in
the closed ball of radius `R`.

## Exponent arithmetic

Young's inequality `1 + 1/r = 1/q + 1/s` with target `r = 3/2` reads `1/q + 1/s = 5/3`.
The kernel `N` has the size `‖z‖⁻¹`, so its truncation lies in `L^s` exactly for `s < 3`; this
allows every `q ≥ 1`.  The kernel `∂ⱼN` has the size `‖z‖⁻²`, so its truncation lies in `L^s`
exactly for `s < 3/2`; this allows exactly `q > 1`.  Both ranges contain the symmetric choice
`q = s = 6/5`, which is the Young instance available as
`eLpNorm_scalarConvolution_six_fifths_three_halves`.  Since the data is compactly supported,
`L^q ⊆ L^{6/5}` for every `q ≥ 6/5`, so all the estimates below are routed through `q = 6/5`
and therefore cover every exponent `q ≥ 6/5`; in particular `q = 3/2` and the exponents
`q > 5/2` of `def:sws`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-! ### A measurable representative supported in the same ball

The force datum of a suitable weak solution is only almost everywhere strongly measurable, while
Young's inequality is stated for measurable data.  Replacing the datum by the indicator of the
support ball of a strongly measurable representative changes neither its `L^p` sizes nor any of
its Newtonian potentials. -/

/-- Data that vanishes off a closed ball and is almost everywhere strongly measurable agrees
almost everywhere with measurable data that vanishes off the same ball. -/
theorem exists_measurable_representative_of_support_closedBall
    {G : Vec3 → ℝ} {R : ℝ} (hG : AEStronglyMeasurable G volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    ∃ G' : Vec3 → ℝ, Measurable G' ∧ G =ᵐ[volume] G' ∧
      (∀ y, y ∉ closedBall (0 : Vec3) R → G' y = 0) := by
  classical
  refine ⟨(closedBall (0 : Vec3) R).indicator (hG.mk G), ?_, ?_, ?_⟩
  · exact (hG.stronglyMeasurable_mk.measurable).indicator isClosed_closedBall.measurableSet
  · filter_upwards [hG.ae_eq_mk] with y hy
    by_cases hyB : y ∈ closedBall (0 : Vec3) R
    · rw [Set.indicator_of_mem hyB, hy]
    · rw [Set.indicator_of_notMem hyB, hGzero y hyB]
  · intro y hy
    rw [Set.indicator_of_notMem hy]

/-! ### Young's inequality on a ball

Data supported in the closed ball of radius `R` only sees the kernel on the ball of radius
`R + ρ` when the potential is evaluated on the ball of radius `ρ`, so the potential agrees there
with the convolution against the truncated kernel, to which the `L^{6/5} * L^{6/5} → L^{3/2}`
Young estimate applies. -/

/-! ### Local `L^{3/2}` membership on the ambient balls -/

end CKN.Foundation.Euclidean
