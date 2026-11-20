/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.NullArray
import Tengoku.Seed.MeasureTheory.Measure.IntegralCharFun

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `thm:increments-levy`, part two: the truncation inequality

Home: line:thm:increments-levy

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`, the second step of the
proof ("two bounds, uniform in `n`"), `eq:truncation`.

The masses of the partition measures `Π_n` diverge — `Π_n(ℝ) = n` — so a limit can only be taken
after weighting, and the weight `1 ∧ x²` is what makes the weighted masses bounded. Both the
bound on those masses and the tightness that keeps mass from escaping to infinity come from a
single inequality, and this file proves it.

## The inequality, and where the Fubini step comes from

For a symmetric probability measure `ρ` with positive transform, and `r > 0`,

  `∫ (1 - sinc(r x)) dρ(x) = (2r)⁻¹ ∫_{-r}^{r} (1 - ρ̂(ω)) dω ≤ (2r)⁻¹ ∫_{-r}^{r} g_ρ(ω) dω`,

where `g_ρ = -log ρ̂`. The first equality is the blueprint's Tonelli step, and it is **not**
proved here: Mathlib carries it as `MeasureTheory.integral_charFun_Icc`, which states
`∫_{-r}^{r} charFun ρ = 2r ∫ sinc(r x) dρ` for a finite measure and does the swap internally.
The inequality is `1 - u ≤ -log u` for `u > 0`, that is `Real.log_le_sub_one_of_pos`.

Summing over the partition, and using additivity for `Σ_i g_i = g_{s,t}`, gives `eq:truncation`
for `Π_n` with a right-hand side independent of `n`:

  `∫ (1 - sinc(r x)) dΠ_n(x) ≤ meanExponent r`, where
  `meanExponent r = (2r)⁻¹ ∫_{-r}^{r} g_{s,t}(ω) dω`.

Combined with `one_sub_sinc_ge` (`Truncation`) this bounds `∫ (1 ∧ x²) dΠ_n`
at `r = 1` and `Π_n{|x| > R}` at `r = 1/R`; and `meanExponent r → 0` as `r ↓ 0` because
`g_{s,t}` is continuous at the origin and vanishes there, which is where the continuity of the
transform does quantitative work.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Tightness.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter Finset
open scoped ENNReal Topology

/-! ## The truncation inequality for one kernel -/

/-- `sinc (r x)` is integrable against a finite measure: it is continuous and bounded by `1`.
@isnad1 id=integrab.0h2v.s5.69b183274185 from=translated src=- shape=5c9ad075 vocab=18888f36
-/
lemma integrable_sinc_mul (ρ : Measure ℝ) [IsFiniteMeasure ρ] (r : ℝ) :
    Integrable (fun x : ℝ => Real.sinc (r * x)) ρ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using Real.abs_sinc_le_one (r * x)

/-- The transform of a symmetric measure, integrated over a symmetric interval, is what
`integral_charFun_Icc` computes: `∫_{-r}^{r} ρ̂ = 2r ∫ sinc(r x) dρ`, read on the real line.
@isnad1 id=eq.2h2v.s6.22f50975bc9a from=translated src=- shape=1c52b2ad vocab=92318e97
-/
lemma intervalIntegral_fourierCos_eq (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hsym : IsSymmetric ρ)
    {r : ℝ} (hr : 0 < r) :
    ∫ ω in (-r)..r, fourierCos ρ ω = 2 * r * ∫ x, Real.sinc (r * x) ∂ρ := by
  have h := integral_charFun_Icc (μ := ρ) hr
  rw [show (fun ω : ℝ => charFun ρ ω) = fun ω : ℝ => ((fourierCos ρ ω : ℝ) : ℂ) from
    funext fun ω => charFun_eq_fourierCos_of_symmetric hsym ω] at h
  rw [intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-! ## The truncation inequality along the partition -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ} {s t : ℝ}

/-- `meanExponent`: the mean of `g_{s,t}` over `[-r,r]`, the blueprint's `ḡ(r)`.-/
noncomputable def meanExponent (μ : ℝ → ℝ → Measure ℝ) (s t r : ℝ) : ℝ :=
  (2 * r)⁻¹ * ∫ ω in (-r)..r, exponent (μ s t) ω

/-! ## The mean exponent vanishes at the origin

This is where the continuity of `g_{s,t}` at `ω = 0`, with `g_{s,t}(0) = 0`, does quantitative
work: it is what forbids escape of mass in the limit.
-/

end ScaleSpace
