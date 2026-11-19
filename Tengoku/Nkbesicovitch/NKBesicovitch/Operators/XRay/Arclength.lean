/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
public import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Map
public import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Add
public import Tengoku.Seed.Analysis.Normed.Module.Basic
public import Tengoku.Seed.Tactic.FunProp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arclength and the vertical line parameter

Normalizing a nonzero direction multiplies the full line integral by
its norm. The identity uses nonnegative extended integrals and remains
valid when either side is infinite.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=eq.2h4v.s8.0bcb7a642f39 from=translated src=- shape=53b1297f vocab=48610ee2
-/
theorem lintegral_normalize_direction {f : E → ℝ≥0∞} (hf : Measurable f)
    {w : E} (hw : w ≠ 0) (x : E) :
    (∫⁻ s : ℝ, f (x + s • (‖w‖⁻¹ • w))) =
      ENNReal.ofReal ‖w‖ * ∫⁻ t : ℝ, f (x + t • w) := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hm : Measurable (fun t : ℝ ↦ f (x + t • w)) := hf.comp (by fun_prop)
  have h := lintegral_map (μ := volume) hm (g := fun s : ℝ ↦ ‖w‖⁻¹ * s) (by fun_prop)
  rw [Real.map_volume_mul_left (inv_ne_zero hn), inv_inv, abs_norm,
    lintegral_smul_measure] at h
  simpa only [smul_smul, smul_eq_mul, mul_comm] using h.symm

end NKBesicovitch.XRay
