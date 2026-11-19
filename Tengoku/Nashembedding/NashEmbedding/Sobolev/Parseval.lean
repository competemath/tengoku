/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Periodization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parseval's identity for continuous periodic functions

For `f : ℝⁿ → ℂ` continuous and `2πℤⁿ`-periodic,
    ∑_{m ∈ ℤⁿ} |ĉ_m|² = (2π)⁻ⁿ ∫_{[0,2π]ⁿ} |f|²,
where `ĉ_m = stdFourierCoeff n f m = (2π)⁻ⁿ ∫_{[0,2π]ⁿ} f e^{-i m·θ}`.

Route: `toUnitTorusCM n f` is a continuous function on Mathlib's `UnitAddTorus (Fin n)`;
its Mathlib Fourier coefficients are `stdFourierCoeff n f` (`mFourierCoeff_toUnitTorusCM`);
Mathlib's `hasSum_sq_mFourierCoeff` on `L²` (via `mFourierCoeff_toLp`) gives the identity
with the torus integral of `|f|²`, which `integral_periodCube_eq_torus` converts to the
cube integral.
-/

open scoped BigOperators
open Real MeasureTheory

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

-- Mathlib's Fourier theory on `UnitAddTorus` normalises `ℝ/ℤ` to have total volume `1`;
-- we bring that measure-space structure (and its basic properties) into scope here.
attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The volume measure on the unit torus is the product of the Haar measures on `ℝ/ℤ`.
@isnad1 id=eq.0h1v.s6.1373b9be8269 from=translated src=- shape=161e228b vocab=48fd7bc0
-/
lemma volume_unitAddTorus :
    (volume : Measure (UnitAddTorus (Fin n)))
      = Measure.pi fun _ : Fin n => AddCircle.haarAddCircle := rfl

end NashEmbedding.Sobolev

end
