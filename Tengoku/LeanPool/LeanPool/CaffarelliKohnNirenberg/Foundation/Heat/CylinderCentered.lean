/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Cylinder
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import Tengoku

/-!
# The backward Gaussian test function at a general base point

For a base point `z₀ = (x₀, t₀)` the paper's backward Gaussian test function of
`eq:psi-r` is `ψ_r(x, t) = r² G(x - x₀, r² - (t - t₀))`, the translate of the
canonical-center function `backwardHeatTestFunction`.  This file records the
translated test function and proves the statements of `eq:psi-backward`,
`eq:psi-lower`, `eq:psi-upper`, `eq:grad-psi`, and `eq:psi-far` of
`paper/ckn.tex` at an arbitrary base point, keeping the constants of the
canonical-center statements exactly.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory Set Filter

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-- The backward Gaussian test function `ψ_r` of `eq:psi-r` based at
`z₀ = (x₀, t₀)`, namely `x ↦ r² G(x - x₀, r² - (t - t₀))` on a parabolic
point `z = (x, t)`. -/
def centeredBackwardHeatTest (x₀ : Vec3) (t₀ r : ℝ) (z : ParabolicPoint) : ℝ :=
  backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀)

/-- The Euclidean norm `|∇ψ_r|` of `eq:grad-psi` for the backward Gaussian test
function based at `z₀ = (x₀, t₀)`. -/
def centeredBackwardHeatTestGradientNorm (x₀ : Vec3) (t₀ r : ℝ)
    (z : ParabolicPoint) : ℝ :=
  backwardHeatTestGradientNorm r (z.1 - x₀) (z.2 - t₀)

private lemma mem_parabolicCylinder_sub_center {x₀ : Vec3} {t₀ r : ℝ}
    {z : ParabolicPoint} :
    z ∈ parabolicCylinder x₀ t₀ r ↔
      (z.1 - x₀, z.2 - t₀) ∈ parabolicCylinder 0 0 r := by
  simp only [mem_parabolicCylinder, sub_zero]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, by linarith only [h₂], by linarith only [h₃]⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, by linarith only [h₂], by linarith only [h₃]⟩

private lemma mem_parabolicCylinder_diff_sub_center {x₀ : Vec3} {t₀ ρ : ℝ}
    {z : ParabolicPoint} :
    z ∈ parabolicCylinder x₀ t₀ ρ \ parabolicCylinder x₀ t₀ (ρ / 2) ↔
      (z.1 - x₀, z.2 - t₀) ∈
        parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2) := by
  constructor
  · intro hz
    exact ⟨mem_parabolicCylinder_sub_center.mp hz.1,
      fun h => hz.2 (mem_parabolicCylinder_sub_center.mpr h)⟩
  · intro hz
    exact ⟨mem_parabolicCylinder_sub_center.mpr hz.1,
      fun h => hz.2 (mem_parabolicCylinder_sub_center.mp h)⟩

/-- `eq:psi-lower`: the backward Gaussian test function based at
`z₀ = (x₀, t₀)` is bounded below by `1/(2000 r)` on the cylinder
`Cyl(r, z₀)`. -/
theorem centeredBackwardHeatTest_lower_on_cylinder {x₀ : Vec3} {t₀ r : ℝ}
    (hr : 0 < r) {z : ParabolicPoint} (hz : z ∈ parabolicCylinder x₀ t₀ r) :
    1 / (2000 * r) ≤ centeredBackwardHeatTest x₀ t₀ r z := by
  have hz' := mem_parabolicCylinder_sub_center.mp hz
  simpa only [centeredBackwardHeatTest] using
    backwardHeatTestFunction_lower_on_cylinder hr hz'

/-- `eq:psi-upper`, first part: the backward Gaussian test function based at
`z₀ = (x₀, t₀)` is bounded above by `1000/r` on the cylinder `Cyl(ρ, z₀)`. -/
theorem centeredBackwardHeatTest_upper_on_cylinder {x₀ : Vec3} {t₀ r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) {z : ParabolicPoint}
    (hz : z ∈ parabolicCylinder x₀ t₀ ρ) :
    centeredBackwardHeatTest x₀ t₀ r z ≤ 1000 / r := by
  have hz' := mem_parabolicCylinder_sub_center.mp hz
  simpa only [centeredBackwardHeatTest] using
    backwardHeatTestFunction_upper_on_cylinder (r := r) (ρ := ρ) hr hρ hz'

/-- `eq:psi-far`, first part: the backward Gaussian test function based at
`z₀ = (x₀, t₀)` is bounded above by `8000000 r²/ρ³` on the annulus
`Cyl(ρ, z₀) \ Cyl(ρ/2, z₀)` when `r ≤ ρ/2`. -/
theorem centeredBackwardHeatTest_upper_on_annulus {x₀ : Vec3} {t₀ r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ / 2) {z : ParabolicPoint}
    (hz : z ∈ parabolicCylinder x₀ t₀ ρ \ parabolicCylinder x₀ t₀ (ρ / 2)) :
    centeredBackwardHeatTest x₀ t₀ r z ≤ 8000000 * r ^ 2 / ρ ^ 3 := by
  have hz' := mem_parabolicCylinder_diff_sub_center.mp hz
  simpa only [centeredBackwardHeatTest] using
    backwardHeatTestFunction_upper_on_annulus (r := r) (ρ := ρ) hr hρ hscale hz'

/-- `eq:psi-far` and `eq:grad-psi`: the gradient norm of the backward Gaussian
test function based at `z₀ = (x₀, t₀)` is bounded above by `5000000 r²/ρ⁴` on
the annulus `Cyl(ρ, z₀) \ Cyl(ρ/2, z₀)` when `r ≤ ρ/2`. -/
theorem centeredBackwardHeatTestGradient_upper_on_annulus {x₀ : Vec3}
    {t₀ r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ / 2)
    {z : ParabolicPoint}
    (hz : z ∈ parabolicCylinder x₀ t₀ ρ \ parabolicCylinder x₀ t₀ (ρ / 2)) :
    centeredBackwardHeatTestGradientNorm x₀ t₀ r z ≤ 5000000 * r ^ 2 / ρ ^ 4 := by
  have hz' := mem_parabolicCylinder_diff_sub_center.mp hz
  simpa only [centeredBackwardHeatTestGradientNorm] using
    backwardHeatTestGradient_upper_on_annulus (r := r) (ρ := ρ) hr hρ hscale hz'

end CKN.Foundation.Heat
