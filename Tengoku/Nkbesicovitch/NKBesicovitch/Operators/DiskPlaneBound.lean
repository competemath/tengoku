/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.DiskRotation
public import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Basic
public import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive disk averages from signed full-plane integrals

For a nonnegative real Schwartz input, the absolute signed plane integral
is the full nonnegative integral. Restriction to the unit disk can only
decrease it, and intrinsic disk volume supplies a direction-independent factor.
-/

public section

open MeasureTheory Set Metric
open scoped SchwartzMap ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

/-- Positivity lets the full signed integral control the normalized unit-disk average.
@isnad1 id=le.1h5v.s13.ca9e3db26555 from=translated src=- shape=f14a57b6 vocab=aabc7c3d
-/
theorem diskAverage_ofReal_le_enorm_integral (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ))
    (hf : ∀ x, 0 ≤ f x) (V : Grassmannian n k) (a : EuclideanSpace ℝ (Fin n)) :
    diskAverage (fun x ↦ ENNReal.ofReal (f x)) V a ≤
      ‖∫ w : V.val, (f (a + w) : ℂ)‖ₑ /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  let g := SchwartzMap.compCLMOfAntilipschitz ℝ (g := fun w : V.val ↦ a + w)
    ((Function.HasTemperateGrowth.const a).add V.val.subtypeL.hasTemperateGrowth)
    (((IsometryEquiv.addLeft a).isometry.comp V.val.subtypeₗᵢ.isometry).antilipschitzWith) f
  have hi : Integrable (fun w : V.val ↦ f (a + w)) volume := g.integrable
  have he : ‖∫ w : V.val, (f (a + w) : ℂ)‖ₑ = ∫⁻ w : V.val, ENNReal.ofReal (f (a + w)) := by
    rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun w : V.val ↦ hf (a + w))]
    exact ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun w ↦ hf (a + w))
  rw [diskAverage, Grassmannian.volume_closedBall, he]
  exact ENNReal.div_le_div_right (setLIntegral_le_lintegral _ _) _

end NKBesicovitch
