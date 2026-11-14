/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.PathIntegral
import Tengoku.Seed.Analysis.Complex.HasPrimitives
import Tengoku.Seed.MeasureTheory.Integral.CurveIntegral.Poincare

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cauchy theorems from primitives

This file proves the path-independence and triangle-boundary consequences that are currently
supported by Mathlib's primitive API.  Mathlib proves existence of primitives on balls and on the
whole plane, but not yet on arbitrary simply connected open sets.  Consequently the holomorphic
triangle theorem below is intentionally stated on a ball; no general simply-connected theorem is
claimed.
-/

open Set Metric MeasureTheory AffineMap Convex
open scoped Interval unitInterval

namespace SandronesLibrary.ComplexAnalysis

/-- Integrating a function with a primitive along a sufficiently regular path gives the difference
of the primitive at the endpoints.  Differentiability and integrability of the parametrization are
spelled out, so this theorem does not silently treat every continuous `Path` as piecewise `C¹`.

> **Entry**: complex-analysis.cauchy.path-independence-primitive-/
theorem pathIntegral_eq_sub_of_primitive
    {f g : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} (gamma : Path a b)
    (hmem : MapsTo gamma.extend (uIcc 0 1) U)
    (hdiff : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ gamma.extend t)
    (hint : IntervalIntegrable
      (fun t : ℝ ↦ deriv gamma.extend t * f (gamma.extend t)) volume 0 1)
    (hg : ∀ z ∈ U, HasDerivAt g (f z) z) :
    pathIntegral f gamma = g b - g a := by
  rw [pathIntegral, curveIntegral_eq_intervalIntegral_deriv]
  change (∫ t : ℝ in 0..1, deriv gamma.extend t * f (gamma.extend t)) = g b - g a
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun t : ℝ ↦ g (gamma.extend t))
    (f' := fun t : ℝ ↦ deriv gamma.extend t * f (gamma.extend t)) (by
      intro t ht
      have houter := hg _ (hmem ht)
      have hinner := (hdiff t ht).hasDerivAt
      simpa [Function.comp_def, mul_comm] using
        (houter.comp_hasFDerivAt t hinner.hasFDerivAt).hasDerivAt) hint
  simpa using hftc

/-- For an exact one-form, two regular paths with the same endpoints have equal integrals.  The
homotopy argument records the textbook situation, although exactness proves the stronger statement
without using the particular homotopy.

> **Entry**: complex-analysis.cauchy.path-independence-primitive-/
theorem pathIntegral_homotopyInvariant_of_primitive
    {f g : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} {gamma delta : Path a b}
    (_homotopy : (gamma : C(Icc (0 : ℝ) 1, ℂ)).Homotopy delta)
    (hgammaMem : MapsTo gamma.extend (uIcc 0 1) U)
    (hdeltaMem : MapsTo delta.extend (uIcc 0 1) U)
    (hgammaDiff : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ gamma.extend t)
    (hdeltaDiff : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ delta.extend t)
    (hgammaInt : IntervalIntegrable
      (fun t : ℝ ↦ deriv gamma.extend t * f (gamma.extend t)) volume 0 1)
    (hdeltaInt : IntervalIntegrable
      (fun t : ℝ ↦ deriv delta.extend t * f (delta.extend t)) volume 0 1)
    (hg : ∀ z ∈ U, HasDerivAt g (f z) z) :
    pathIntegral f gamma = pathIntegral f delta := by
  rw [pathIntegral_eq_sub_of_primitive gamma hgammaMem hgammaDiff hgammaInt hg,
    pathIntegral_eq_sub_of_primitive delta hdeltaMem hdeltaDiff hdeltaInt hg]

/-- The primitive endpoint formula specialized to a line segment.

> **Entry**: complex-analysis.cauchy.triangle-ball-/
theorem pathIntegral_segment_eq_sub_of_primitive
    {f g : ℂ → ℂ} {U : Set ℂ} {a b : ℂ}
    (hseg : [a -[ℝ] b] ⊆ U) (hf : ContinuousOn f U)
    (hg : ∀ z ∈ U, HasDerivAt g (f z) z) :
    pathIntegral f (.segment a b) = g b - g a := by
  rw [pathIntegral_segment]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun t : ℝ ↦ g (lineMap a b t))
    (f' := fun t : ℝ ↦ (b - a) * f (lineMap a b t)) (by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hline : lineMap a b t ∈ [a -[ℝ] b] := lineMap_mem_segment ℝ a b ht
      have houter := hg _ (hseg hline)
      have hinner := (hasDerivAt_lineMap (a := a) (b := b) (x := t)).hasFDerivAt
      simpa [Function.comp_def, mul_comm] using
        (houter.comp_hasFDerivAt t hinner).hasDerivAt) (by
      exact (((hf.mono hseg).comp lineMap_continuous.continuousOn
        (fun t ht ↦ lineMap_mem_segment ℝ a b (by simpa [uIcc_of_le zero_le_one] using ht)))
          |>.const_mul (b - a)).intervalIntegrable)
  simpa using hftc

/-- If `f` has a primitive on a set containing the three edges, its integral around the oriented
triangle boundary is zero.

> **Entry**: complex-analysis.cauchy.triangle-ball-/
theorem pathIntegral_triangle_eq_zero_of_primitive
    {f g : ℂ → ℂ} {U : Set ℂ} {a b c : ℂ}
    (hab : [a -[ℝ] b] ⊆ U) (hbc : [b -[ℝ] c] ⊆ U) (hca : [c -[ℝ] a] ⊆ U)
    (hf : ContinuousOn f U) (hg : ∀ z ∈ U, HasDerivAt g (f z) z) :
    pathIntegral f (.segment a b) + pathIntegral f (.segment b c) +
      pathIntegral f (.segment c a) = 0 := by
  rw [pathIntegral_segment_eq_sub_of_primitive hab hf hg,
    pathIntegral_segment_eq_sub_of_primitive hbc hf hg,
    pathIntegral_segment_eq_sub_of_primitive hca hf hg]
  abel

/-- A holomorphic function on a ball integrates to zero around any triangle whose vertices lie in
the ball.  Convexity keeps all three edges in the ball, and Mathlib supplies a primitive there.

> **Entry**: complex-analysis.cauchy.triangle-ball-/
theorem pathIntegral_triangle_eq_zero_of_holomorphicOnTextbook_ball
    {f : ℂ → ℂ} {center a b c : ℂ} {r : ℝ}
    (hf : HolomorphicOnTextbook f (ball center r))
    (ha : a ∈ ball center r) (hb : b ∈ ball center r) (hc : c ∈ ball center r) :
    pathIntegral f (.segment a b) + pathIntegral f (.segment b c) +
      pathIntegral f (.segment c a) = 0 := by
  have hdiff : DifferentiableOn ℂ f (ball center r) :=
    (holomorphicOnTextbook_iff_differentiableOn isOpen_ball).mp hf
  obtain ⟨g, hg⟩ := hdiff.isExactOn_ball
  exact pathIntegral_triangle_eq_zero_of_primitive
    ((convex_ball center r).segment_subset ha hb)
    ((convex_ball center r).segment_subset hb hc)
    ((convex_ball center r).segment_subset hc ha) hdiff.continuousOn hg

end SandronesLibrary.ComplexAnalysis
