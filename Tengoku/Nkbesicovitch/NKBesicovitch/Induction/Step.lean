/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.PlateIntegral
public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.FlagMeasure
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlateRotation
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.MixedNorm.MapProd
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.Frame

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The plate-to-X-ray step of the induction

A lower-dimensional plate estimate applied to each frame X-ray transform
controls the higher-dimensional plate norm. The flag probability identity
and upper integral inequalities suffice without a measurability assumption
on either plate supremum. The lower-dimensional inputs remain in a fixed
ball, and the exact frame identity gives the spherical X-ray norm.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian NKBesicovitch.XRay
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/--
@isnad1 id=le.2h9v.s13.e13331c7aaeb from=translated src=- shape=d55da63a vocab=35b59416
-/
theorem plateMaximal_flagDirection_le {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) {δ : ℝ} (hδ : 0 < δ) (u : Rotations n) (V : Grassmannian m k) :
    plateMaximal δ f (flagDirection (norm_eq_of_mem_sphere v) b (u, V)) ≤
      (2 : ℝ≥0∞) ^ m * plateMaximal δ (frameXRay v b f u) V := by
  rw [flagDirection, plateMaximal_rotate]
  exact plateMaximal_normalLift_le (norm_eq_of_mem_sphere v) b V hδ
    (hf.comp (Unitary.linearIsometryEquiv u).continuous.measurable)

end NKBesicovitch.Induction
