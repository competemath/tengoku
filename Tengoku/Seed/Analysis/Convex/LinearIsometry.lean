/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Convex.ContinuousLinearEquiv
public import Tengoku.Seed.Analysis.Convex.StrictConvexSpace
public import Tengoku.Seed.Analysis.Normed.Operator.LinearIsometry

/-!
# (Strict) convexity and linear isometries

In this file we prove some basic lemmas about (strict) convexity and linear isometries.
-/

public section

open Set Metric
open scoped Convex

section SeminormedAddCommGroup

variable {𝕜 E F : Type*}
  [NormedField 𝕜] [PartialOrder 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
@isnad1 id=iff.0h5v.s9.8253d3e4fbff from=seed src=0 shape=a5cc53ac vocab=9d6a54bf
-/
@[simp]
lemma LinearIsometryEquiv.strictConvex_preimage {s : Set F} (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s :=
  e.toContinuousLinearEquiv.strictConvex_preimage

/--
@isnad1 id=iff.0h5v.s9.feef1803f96e from=seed src=0 shape=3e792043 vocab=92e14a66
-/
@[simp]
lemma LinearIsometryEquiv.strictConvex_image {s : Set E} (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s :=
  e.toContinuousLinearEquiv.strictConvex_image

end SeminormedAddCommGroup

variable {𝕜 E F : Type*} [NormedField 𝕜] [PartialOrder 𝕜]

/--
@isnad1 id=strictco.1h5v.s8.f09bc56d37a9 from=seed src=0 shape=63e4446f vocab=9454de9e
-/
lemma StrictConvex.linearIsometry_preimage [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set F}
    (hs : StrictConvex 𝕜 s) (e : E →ₗᵢ[𝕜] F) : StrictConvex 𝕜 (e ⁻¹' s) :=
  hs.linear_preimage _ e.continuous e.injective

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
@isnad1 id=iff.0h4v.s6.63f677899849 from=seed src=0 shape=1e113fd2 vocab=5dd06b5e
-/
protected lemma LinearIsometryEquiv.strictConvexSpace_iff (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 E ↔ StrictConvexSpace 𝕜 F := by
  simp only [strictConvexSpace_iff, ← map_zero e, ← e.image_closedBall, e.strictConvex_image]

/--
@isnad1 id=iff.0h4v.s9.76a6892d1fd9 from=seed src=0 shape=5dcb7fc9 vocab=a5a1d5ff
-/
lemma LinearIsometry.strictConvexSpace_range_iff (e : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 (e : E →ₗ[𝕜] F).range ↔ StrictConvexSpace 𝕜 E :=
  e.equivRange.strictConvexSpace_iff.symm

/--
@isnad1 id=strictco.0h4v.s9.2f8f6fa0ccde from=seed src=0 shape=ee914753 vocab=a5a1d5ff
-/
instance LinearIsometry.strictConvexSpace_range [StrictConvexSpace 𝕜 E] (e : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 (e : E →ₗ[𝕜] F).range :=
  e.strictConvexSpace_range_iff.mpr ‹_›

/--
@isnad1 id=strictco.0h4v.s6.04b0f38a6cde from=seed src=0 shape=9704c3c0 vocab=a4267033
-/
lemma LinearIsometry.strictConvexSpace [StrictConvexSpace 𝕜 F] (f : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 E where
  strictConvex_closedBall r hr := by
    rw [← f.isometry.preimage_closedBall]
    exact (strictConvex_closedBall _ _ _).linearIsometry_preimage _

/-- A vector subspace of a strict convex space is a strict convex space.

This instance has priority 900
to make sure that instances like `LinearIsometry.strictConvexSpace_range`
are tried before this one.
@isnad1 id=strictco.0h3v.s7.29d4921903c4 from=seed src=0 shape=046352a6 vocab=30d43665
-/
instance (priority := 900) Submodule.instStrictConvexSpace [StrictConvexSpace 𝕜 E]
    (p : Submodule 𝕜 E) : StrictConvexSpace 𝕜 p :=
  p.subtypeₗᵢ.strictConvexSpace
