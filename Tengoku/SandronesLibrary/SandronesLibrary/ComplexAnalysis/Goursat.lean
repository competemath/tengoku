/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.CauchyTheorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Cauchy--Goursat theorem on a triangle

This file removes the ball restriction from `CauchyTheorem.lean`.  The closed triangle is
represented by the real convex hull of its three vertices.  Mathlib's Poincare lemma gives a
relative primitive on this convex set; a relative endpoint formula then proves that the three
oriented edge integrals cancel.

Current entry:

* `complex-analysis.cauchy.triangle`: the local triangle form of Cauchy--Goursat.
-/

open Set Metric MeasureTheory AffineMap Convex Filter
open scoped Interval unitInterval

namespace SandronesLibrary.ComplexAnalysis

/-- A primitive defined only within a convex set still gives the endpoint formula along every
segment in that set.  The use of `HasDerivWithinAt` is essential at boundary points of a closed
triangle.

> **Entry**: complex-analysis.cauchy.triangle
@isnad1 id=eq.5h5v.s7.2e7b44afa638 from=translated src=- shape=d2f4b8e2 vocab=6458ee49
-/
theorem pathIntegral_segment_eq_sub_of_primitiveWithin_convex
    {f g : ℂ → ℂ} {T : Set ℂ} {a b : ℂ}
    (hT : Convex ℝ T) (ha : a ∈ T) (hb : b ∈ T)
    (hf : ContinuousOn f T)
    (hg : ∀ z ∈ T, HasDerivWithinAt g (f z) T z) :
    pathIntegral f (.segment a b) = g b - g a := by
  rw [pathIntegral_segment]
  have hline : MapsTo (lineMap a b) (Icc (0 : ℝ) 1) T :=
    fun _ ht ↦ hT.lineMap_mem ha hb ht
  have hcont : ContinuousOn (fun t : ℝ ↦ g (lineMap a b t)) (Icc 0 1) := by
    exact ContinuousOn.comp
      (fun z hz ↦ (hg z hz).continuousWithinAt) lineMap_continuous.continuousOn hline
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ g (lineMap a b t)) ((b - a) * f (lineMap a b t)) t := by
    intro t ht
    have htT : lineMap a b t ∈ T := hline ⟨ht.1.le, ht.2.le⟩
    have hevent : ∀ᶠ s : ℝ in nhds t, lineMap a b s ∈ T := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hline ⟨hs.1.le, hs.2.le⟩
    simpa [Function.comp_def, mul_comm] using
      (hg _ htT).comp_hasDerivAt t hasDerivAt_lineMap hevent
  have hint : IntervalIntegrable (fun t : ℝ ↦ (b - a) * f (lineMap a b t)) volume 0 1 := by
    have hc : ContinuousOn (fun t : ℝ ↦ (b - a) * f (lineMap a b t)) (Icc 0 1) := by
      simpa [Function.comp_def] using
        (ContinuousOn.comp hf lineMap_continuous.continuousOn hline).const_mul (b - a)
    exact (show ContinuousOn (fun t : ℝ ↦ (b - a) * f (lineMap a b t)) [[0, 1]] by
      simpa [uIcc_of_le zero_le_one] using hc).intervalIntegrable
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint

/-- **Cauchy--Goursat on a triangle.** If `f` is textbook-holomorphic on an open set containing
the closed real convex hull of `a`, `b`, and `c`, then its integral around the oriented triangle
boundary is zero.  Unlike the earlier foundation theorem, the ambient open set need not be a ball.

> **Entry**: complex-analysis.cauchy.triangle
@isnad1 id=eq.3h5v.s8.32581f9f2582 from=translated src=- shape=bb74f85f vocab=5a7e292b
-/
theorem pathIntegral_triangle_eq_zero_of_holomorphicOnTextbook
    {f : ℂ → ℂ} {U : Set ℂ} {a b c : ℂ}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (htriangle : convexHull ℝ ({a, b, c} : Set ℂ) ⊆ U) :
    pathIntegral f (.segment a b) + pathIntegral f (.segment b c) +
      pathIntegral f (.segment c a) = 0 := by
  let T : Set ℂ := convexHull ℝ ({a, b, c} : Set ℂ)
  have hT : Convex ℝ T := convex_convexHull ℝ _
  have ha : a ∈ T := by
    apply subset_convexHull ℝ
    simp
  have hb : b ∈ T := by
    apply subset_convexHull ℝ
    simp
  have hc : c ∈ T := by
    apply subset_convexHull ℝ
    simp
  have hdiffU : DifferentiableOn ℂ f U :=
    (holomorphicOnTextbook_iff_differentiableOn hU).mp hf
  have hdiffT : DifferentiableOn ℂ f T := hdiffU.mono htriangle
  obtain ⟨g, hg⟩ := hT.exists_forall_hasDerivWithinAt hdiffT
  rw [pathIntegral_segment_eq_sub_of_primitiveWithin_convex hT ha hb hdiffT.continuousOn hg,
    pathIntegral_segment_eq_sub_of_primitiveWithin_convex hT hb hc hdiffT.continuousOn hg,
    pathIntegral_segment_eq_sub_of_primitiveWithin_convex hT hc ha hdiffT.continuousOn hg]
  abel

end SandronesLibrary.ComplexAnalysis
