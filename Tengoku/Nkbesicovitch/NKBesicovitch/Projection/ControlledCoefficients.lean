/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.PatternControl
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.PatternCodeImages
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.PatternOuter
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.ControlMonomials

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit inner and outer constants for controlled patterns

The common separation and input constant determine both analytic
coefficients, independently of the chosen pattern. These formulas retain
only powers, products, and quotients of positive quantities, making their
polynomial dependence available to the finite-tree stopping argument.
-/

@[expose] public section

open MeasureTheory Set Bornology

namespace NKBesicovitch.Projection

namespace CornerPattern.IsControlled

variable {m L : ℕ} {β r C : ℝ} {P : CornerPattern m β}

/--
@isnad1 id=codeimag.3h6v.s7.a10339259b8c from=translated src=- shape=f55e8104 vocab=b8f0d945
-/
theorem codeImageBound (h : P.IsControlled r C L) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    P.CodeImageBound ((2 * r⁻¹ ^ m * C) ^ (1 / (β - 1)) / (r ^ m) ^ (β / (β - 1))) := by
  have hr := h.radius_pos
  have hC := zero_lt_one.trans_le h.one_le_constant
  have hβ1 := sub_pos.mpr hβ
  apply (P.codeImageBound_of_input_bound hβ hβ2 hC (pow_pos hr m) h.inner_bound
    (fun _ hu _ ht ↦ h.innerJacobian_ge hu ht)).mono
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h.reverse_codeJacobian_le (by norm_num)) hC.le

/--
@isnad1 id=outerbou.3h6v.s7.25cda989ed6f from=translated src=- shape=61ed7152 vocab=e1689093
-/
theorem outerBound (h : P.IsControlled r C L) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    P.OuterBound (((2 * (r⁻¹ ^ m) ^ 2 * C) * (r⁻¹ ^ m) ^ (β - 1)) ^ (1 / (β - 1))) := by
  have hr := h.radius_pos
  have hC := zero_lt_one.trans_le h.one_le_constant
  have hβ1 := sub_pos.mpr hβ
  apply (P.outerBound_of_input_bound hβ hβ2 hC h.outer_bound).mono
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  apply mul_le_mul _ (Real.rpow_le_rpow ENNReal.toReal_nonneg h.codeJacobian_le hβ1.le)
    (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg h.codeJacobian_le 2)
      (by norm_num)) hC.le

/--
@isnad1 id=codeimag.3h6v.s5.f98a172b0b80 from=translated src=- shape=3b690b34 vocab=2fe309d5
-/
theorem codeImageBound_controlCoefficient (h : P.IsControlled r C L) (hβ : 1 < β)
    (hβ2 : β ≤ 2) : P.CodeImageBound (controlCoefficient m β r C) := by
  simpa only [inner_controlCoefficient_eq m β h.radius_pos
    (zero_lt_one.trans_le h.one_le_constant)] using h.codeImageBound hβ hβ2

/--
@isnad1 id=outerbou.3h6v.s5.920d901ed4d4 from=translated src=- shape=3b690b34 vocab=57cfeaea
-/
theorem outerBound_controlCoefficient (h : P.IsControlled r C L) (hβ : 1 < β)
    (hβ2 : β ≤ 2) : P.OuterBound (controlCoefficient m β r C) := by
  simpa only [outer_controlCoefficient_eq m β h.radius_pos
    (zero_lt_one.trans_le h.one_le_constant)] using h.outerBound hβ hβ2

end CornerPattern.IsControlled

end NKBesicovitch.Projection
