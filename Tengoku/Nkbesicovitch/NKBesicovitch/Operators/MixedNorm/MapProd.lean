/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.MixedNorm.Basic
public import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Upper norm bounds under maps and product integration

The inequalities for lower Lebesgue integrals suffice for upper norm
estimates without measurability assumptions on the integrand. In the
induction this avoids assuming that an uncountable plate supremum is
measurable before bounding it by the lower-dimensional estimate.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p : ℝ≥0∞}

/--
@isnad1 id=le.2h6v.s6.b491496ce9c5 from=translated src=- shape=daf250d4 vocab=94146233
-/
theorem eLpNorm_map_le (g : X → Y) (f : Y → ℝ≥0∞) (hp : p ≠ 0) (hpfin : p ≠ ∞) :
    eLpNorm f p (μ.map g) ≤ eLpNorm (f ∘ g) p μ := by
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin, enorm_eq_self,
    Function.comp_apply]
  exact ENNReal.rpow_le_rpow (lintegral_map_le (fun y ↦ f y ^ p.toReal) g) (by positivity)

/--
@isnad1 id=le.2h6v.s6.1d17d61f5804 from=translated src=- shape=6459d99d vocab=24541455
-/
theorem eLpNorm_prod_le_iterated (f : X × Y → ℝ≥0∞)
    (hp : p ≠ 0) (hpfin : p ≠ ∞) :
    eLpNorm f p (μ.prod ν) ≤ eLpNorm (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) p μ := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp hpfin
  have hpow (x : X) : eLpNorm (fun y ↦ f (x, y)) p ν ^ p.toReal =
      ∫⁻ y, f (x, y) ^ p.toReal ∂ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpos.ne', ENNReal.rpow_one]
    simp only [enorm_eq_self]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin]
  simp only [enorm_eq_self, hpow]
  exact ENNReal.rpow_le_rpow (lintegral_prod_le (fun z ↦ f z ^ p.toReal)) (by positivity)

/-- For a measurable nonnegative input, equal iterated exponents give the product norm.
@isnad1 id=eq.3h6v.s6.769dea0de7a0 from=translated src=- shape=bdceb86a vocab=8636c948
-/
theorem eLpNorm_iterated_eq_prod [SFinite ν] {f : X × Y → ℝ≥0∞} (hf : Measurable f)
    (hp : p ≠ 0) (hpfin : p ≠ ∞) :
    eLpNorm (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) p μ = eLpNorm f p (μ.prod ν) := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp hpfin
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin, enorm_eq_self,
    ← ENNReal.rpow_mul, one_div_mul_cancel hpos.ne', ENNReal.rpow_one]
  rw [lintegral_prod _ (hf.pow_const p.toReal).aemeasurable]

end NKBesicovitch
