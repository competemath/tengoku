/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.SpecialFunctions.Pow.Integral
public import Tengoku
-- `Mathlib.MeasureTheory.Measure.Prod` is imported privately: the product measure and
-- Tonelli's theorem appear only inside the proof below.

/-!
# Marcinkiewicz interpolation between weak type `(1,1)` and `L^∞`

A **sublinear** operator `T` that is simultaneously of **weak type `(1,1)`** and bounded on `L^∞`
is bounded on `L^p` for every `1 < p < ∞`. This is the diagonal case `p₀ = 1`, `p₁ = ∞` of the
Marcinkiewicz interpolation theorem, and it is the mechanism that turns the Hardy–Littlewood
maximal inequality into the strong `(p,p)` bounds, item 9 of Lane B of the PDE roadmap.

## The statements proved here

The analytic engine is stated in terms of the **distribution functions** of `T f` and of `f`.
The operator-level theorem then derives its hypothesis from subadditivity, weak type `(1,1)`, and
an `L^∞` bound. For each height `t`, these hypotheses produce the single inequality

`t * ν {T f > t} ≤ d⁻¹ * A * ∫⁻ x in {‖f‖ > c * t}, ‖f‖ ∂μ`,

which says that only the part of `f` above the height `c * t` can push `T f` above `t`. That
inequality is the hypothesis of `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le`, and its
conclusion is the `L^p` bound

`∫⁻ (T f) ^ p ∂ν ≤ (p * c ^ (1 - p) / (p - 1)) * d⁻¹ * A * ∫⁻ ‖f‖ ^ p ∂μ`.

Retaining this distributional lemma keeps the analytic engine usable even when `T` is not defined
on a whole function space. The operator theorem lets `μ` and `ν` live on different spaces and makes
the dependence on the endpoint and splitting constants explicit. Its constant blows up as
`p → 1`, exactly as it must — an operator of weak type `(1,1)` need not be bounded on `L¹`.

## The proof

The layer cake formula (`TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul`) converts both
sides into integrals in the height variable `t`. The hypothesis, multiplied by `t ^ (p - 2)`,
bounds the integrand by `A * t ^ (p - 2) * ∫⁻ x in {‖f‖ > c * t}, ‖f‖ ∂μ`; Tonelli's theorem then
exchanges the `t` and `x` integrations, and for each fixed `x` the inner integral is the
elementary `∫⁻ t in (0, ‖f x‖ / c), t ^ (p - 2) = (‖f x‖ / c) ^ (p - 1) / (p - 1)`, evaluated by
`TauCeti.lintegral_indicator_ofReal_rpow_Ioi`, which reassembles into
`c ^ (1 - p) / (p - 1) * ‖f x‖ ^ p`. Convergence of that inner integral at the origin is where
`1 < p` is used, and it is why the constant carries the factor `1 / (p - 1)`.

Tonelli's theorem needs `μ` to be s-finite, but the statement does not: both sides ignore the
part of `μ` outside `{f > 0}`, and once `∫⁻ f ^ p ∂μ` is finite that part is σ-finite, being
exhausted by the level sets `{f ≥ 1 / (n + 1)}`, each of finite measure by Chebyshev.

## Main declarations

* `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le`: the interpolation estimate.
* `TauCeti.mul_meas_ofReal_lt_le_setLIntegral`: the reusable truncation argument from
  subadditivity and the two endpoint bounds.
* `TauCeti.lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup`: operator-level
  Marcinkiewicz interpolation.

## References

* L. Grafakos, *Classical Fourier Analysis*, Theorem 1.3.1.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I, §4.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {f : α → ℝ≥0∞} {u : β → ℝ≥0∞} {p c : ℝ} {A : ℝ≥0∞}

section Operator

variable {G : Type*} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G]
  [ESeminormedAddMonoid G] {T : (α → G) → β → ℝ≥0∞} {v : α → G} {b d t : ℝ}

/-- The reusable operator-level truncation argument for Marcinkiewicz interpolation.

Suppose `T` is subadditive, is of weak type `(1,1)` with constant `A`, and obeys the `L^∞`
bound `T g ≤ b · ‖g‖_∞`. Split `v` according to whether its
extended norm exceeds `c * t`. If `b * c + d ≤ 1`, then the low part contributes at most
`b * c * t`, so `T v > t` forces the image of the high part to exceed `d * t`. Applying the
weak-type bound to that high part gives

`t * ν {T v > t} ≤ d⁻¹ * A * ∫⁻ x in {‖v‖ₑ > c * t}, ‖v x‖ₑ ∂μ`.

The parameters `c` and `d` expose the choice of truncation rather than fixing the customary
`c = d = 1 / 2` for a normalized `L^∞` bound. -/
theorem mul_meas_ofReal_lt_le_setLIntegral
    (hv : AEMeasurable v μ) (ht : 0 < t) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (hbcd : b * c + d ≤ 1)
    (hadd : ∀ (g h : α → G), AEMeasurable g μ → AEMeasurable h μ →
      T (g + h) ≤ᵐ[ν] T g + T h)
    (hweak : ∀ (g : α → G), AEMeasurable g μ → ∀ s : ℝ≥0∞,
      s * ν {y | s < T g y} ≤ A * ∫⁻ x, ‖g x‖ₑ ∂μ)
    (hinfty : ∀ (g : α → G), AEMeasurable g μ → T g ≤ᵐ[ν]
      fun _ => ENNReal.ofReal b * eLpNormEssSup g μ) :
    ENNReal.ofReal t * ν {y | ENNReal.ofReal t < T v y} ≤
      ENNReal.ofReal d⁻¹ * A *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ∂μ := by
  have hct : 0 ≤ c * t := (mul_pos hc ht).le
  have hdt : 0 ≤ d * t := (mul_pos hd ht).le
  have hbct : 0 ≤ b * (c * t) := mul_nonneg hb hct
  have hdinv : 0 ≤ d⁻¹ := inv_nonneg.2 hd.le
  set g : α → G := hv.mk v with hgdef
  have hvg : v =ᵐ[μ] g := hv.ae_eq_mk
  have hgmeas : Measurable g := hv.measurable_mk
  set S : Set α := {x | ENNReal.ofReal (c * t) < ‖g x‖ₑ} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const hgmeas.enorm
  set g₁ : α → G := S.indicator v with hg₁def
  set g₂ : α → G := Sᶜ.indicator v with hg₂def
  have hg₁meas : AEMeasurable g₁ μ := hv.indicator hSmeas
  have hg₂meas : AEMeasurable g₂ μ := hv.indicator hSmeas.compl
  have hsplit : g₁ + g₂ = v := by
    rw [hg₁def, hg₂def, Set.indicator_self_add_compl]
  have hTv : T v ≤ᵐ[ν] T g₁ + T g₂ := by
    rw [← hsplit]
    exact hadd g₁ g₂ hg₁meas hg₂meas
  have hg₂bound : ∀ᵐ x ∂μ, ‖g₂ x‖ₑ ≤ ENNReal.ofReal (c * t) := by
    filter_upwards [hvg] with x hx
    rw [hg₂def]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_notMem (by simp [hxS]), enorm_zero]
      exact zero_le
    · rw [Set.indicator_of_mem (by simp [hxS]), hx]
      exact not_lt.1 (by simpa [hSdef] using hxS)
  have hTg₂ : ∀ᵐ y ∂ν, T g₂ y ≤ ENNReal.ofReal (b * (c * t)) := by
    filter_upwards [hinfty g₂ hg₂meas] with y hy
    exact hy.trans (calc
      ENNReal.ofReal b * eLpNormEssSup g₂ μ
          ≤ ENNReal.ofReal b * ENNReal.ofReal (c * t) := by
            gcongr
            exact essSup_le_of_ae_le _ hg₂bound
      _ = ENNReal.ofReal (b * (c * t)) := by rw [ENNReal.ofReal_mul hb])
  have hincl : {y | ENNReal.ofReal t < T v y} ≤ᵐ[ν]
      {y | ENNReal.ofReal (d * t) < T g₁ y} := by
    filter_upwards [hTv, hTg₂] with y hsum hlow
    intro hy
    have hconst : ENNReal.ofReal (d * t) + ENNReal.ofReal (b * (c * t)) ≤
        ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_add hdt hbct]
      gcongr
      nlinarith [mul_nonneg (sub_nonneg.2 hbcd) ht.le]
    have hlt : ENNReal.ofReal (d * t) + ENNReal.ofReal (b * (c * t)) <
        T g₁ y + ENNReal.ofReal (b * (c * t)) :=
      hconst.trans_lt (hy.trans_le (hsum.trans (add_le_add le_rfl hlow)))
    exact (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).1 hlt
  have hint : ∫⁻ x, ‖g₁ x‖ₑ ∂μ =
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ∂μ := by
    have henorm : (fun x => ‖v x‖ₑ) =ᵐ[μ] fun x => ‖g x‖ₑ :=
      hvg.mono fun _ hx => congrArg enorm hx
    have hsets : {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ} =ᵐ[μ] S := by
      filter_upwards [henorm] with x hx
      exact congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (c * t) < z) hx
    calc ∫⁻ x, ‖g₁ x‖ₑ ∂μ
        = ∫⁻ x in S, ‖v x‖ₑ ∂μ := by
          rw [hg₁def]
          simp_rw [enorm_indicator_eq_indicator_enorm]
          exact lintegral_indicator hSmeas _
      _ = ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ∂μ := by
          rw [Measure.restrict_congr_set hsets]
  calc ENNReal.ofReal t * ν {y | ENNReal.ofReal t < T v y}
      = ENNReal.ofReal d⁻¹ *
          (ENNReal.ofReal (d * t) * ν {y | ENNReal.ofReal t < T v y}) := by
        have hscale : d⁻¹ * (d * t) = t := by field_simp
        rw [← mul_assoc, ← ENNReal.ofReal_mul hdinv, hscale]
    _ ≤ ENNReal.ofReal d⁻¹ *
          (ENNReal.ofReal (d * t) * ν {y | ENNReal.ofReal (d * t) < T g₁ y}) := by
        exact mul_le_mul_right
          (mul_le_mul_right (measure_mono_ae hincl) (ENNReal.ofReal (d * t)))
          (ENNReal.ofReal d⁻¹)
    _ ≤ ENNReal.ofReal d⁻¹ * (A * ∫⁻ x, ‖g₁ x‖ₑ ∂μ) := by
        exact mul_le_mul_right
          (hweak g₁ hg₁meas (ENNReal.ofReal (d * t)))
          (ENNReal.ofReal d⁻¹)
    _ = ENNReal.ofReal d⁻¹ * A *
          ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ∂μ := by
        rw [hint, mul_assoc]

end Operator

end TauCeti
