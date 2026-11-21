/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.BochnerConvolutionSpace
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.L1Continuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The modulus of continuity of translation on `L¹(E)`, and the estimate (★)

Home: none (standard analysis in Mathlib's types: the `d`-dimensional counterpart of
`ScaleSpaceCore.L1Continuity`'s estimate, with no programme vocabulary; ref: @engel2000one,
Example 5.4, p. 39)

Q-0332 (SSL-5, stretch), the `d`-dimensional counterpart of `ScaleSpaceCore.L1Continuity`:
`Θ_f(y) = ‖T_y f - f‖₁` is bounded, continuous and vanishes at `0` (`transDiffE`, packaged as
`transDiffBCFE`), and for a probability measure

  `‖μ * f - f‖₁ ≤ ∫ ‖T_y f - f‖₁ μ(dy)`.                                            (★)

On the line (★) is proved by Tonelli; here it is one line from the Bochner form
`μ * f = ∫ T_y f dμ(y)` (`bconvME_eq_mconvL1E`): `μ * f - f = ∫ (T_y f - f) dμ(y)`, and the norm
of an integral is at most the integral of the norm.

Over an inner product space the Lévy clause follows as on the line: kernels whose
characteristic functions tend to `1` give operators tending strongly to the identity
(`tendsto_norm_mconvL1E_sub_of_tendsto_charFun`), through Mathlib's Lévy continuity theorem on a
finite-dimensional inner product space.

## References

* @engel2000one, Example 5.4, p. 39: the translation group's strong continuity on `Lᵖ(ℝ)` — the
  density-of-compactly-supported-functions argument that `transDiffE`'s vanishing at `0` is the
  Haar-measure generalisation of, at `p = 1`. (★) and the Lévy clause are elementary consequences
  once that continuity, and Mathlib's own Lévy continuity theorem, are in hand.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- `Θ_f(y) = ‖T_y f - f‖₁`, the modulus of continuity of translation at `f`.-/
noncomputable def transDiffE (f : E →₁[volume] ℝ) (y : E) : ℝ := ‖transL1E y f - f‖

/--
@isnad1 id=continuo.0h2v.s8.8f169071d4ca from=translated src=- shape=342801dc vocab=c950f5b8
-/
theorem continuous_transDiffE (f : E →₁[volume] ℝ) : Continuous (transDiffE f) :=
  ((continuous_transL1E f).sub continuous_const).norm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/--
@isnad1 id=le.0h3v.s8.47cbe66849e6 from=translated src=- shape=36a0b20c vocab=44169d86
-/
theorem transDiffE_nonneg (f : E →₁[volume] ℝ) (y : E) : 0 ≤ transDiffE f y := norm_nonneg _

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.0h2v.s8.3f294ff3a600 from=translated src=- shape=510097e2 vocab=86bd48d7
-/
@[simp]
theorem transDiffE_zero (f : E →₁[volume] ℝ) : transDiffE f 0 = 0 := by
  rw [transDiffE, transL1E_zero, ContinuousLinearMap.id_apply, sub_self, norm_zero]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `Θ_f ≤ 2‖f‖`.
@isnad1 id=le.0h3v.s9.eb0fe0d7f326 from=translated src=- shape=3b029452 vocab=6b7fbe48
-/
theorem transDiffE_le (f : E →₁[volume] ℝ) (y : E) : transDiffE f y ≤ 2 * ‖f‖ := by
  calc transDiffE f y ≤ ‖transL1E y f‖ + ‖f‖ := norm_sub_le _ _
    _ ≤ 2 * ‖f‖ := by linarith [norm_transL1E_le y f]

/--
@isnad1 id=integrab.0h3v.s8.1d7ca17a1f18 from=translated src=- shape=b4ce16bd vocab=020c40de
-/
theorem integrable_transDiffE (μ : Measure E) [IsFiniteMeasure μ] (f : E →₁[volume] ℝ) :
    Integrable (transDiffE f) μ :=
  (integrable_const (2 * ‖f‖)).mono' (continuous_transDiffE f).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (transDiffE_nonneg f y)]
      exact transDiffE_le f y)

/-- **(★).** `‖μ * f - f‖₁ ≤ ∫ Θ_f dμ` for a probability measure `μ`.
@isnad1 id=le.0h3v.s12.c501e9342699 from=translated src=- shape=b1856021 vocab=115a2ded
-/
theorem norm_mconvL1E_sub_le (μ : Measure E) [IsProbabilityMeasure μ] (f : E →₁[volume] ℝ) :
    ‖mconvL1E μ f - f‖ ≤ ∫ y, transDiffE f y ∂μ := by
  have hsplit : mconvL1E μ f - f = ∫ y, (transL1E y f - f) ∂μ := by
    rw [integral_sub (integrable_transL1E μ f) (integrable_const f), integral_const,
      ← bconvME_eq_mconvL1E, bconvME, probReal_univ, one_smul]
  rw [hsplit]
  exact norm_integral_le_integral_norm _

/-- **The modulus of continuity decreases under convolution**: `Θ_{ν*f} ≤ Θ_f`.
@isnad1 id=le.0h4v.s12.7c2364252301 from=translated src=- shape=8d6d713a vocab=69271ecc
-/
theorem transDiffE_mconvL1E_le (ν : Measure E) [IsProbabilityMeasure ν] (f : E →₁[volume] ℝ)
    (y : E) : transDiffE (mconvL1E ν f) y ≤ transDiffE f y := by
  have hcomm : transL1E y (mconvL1E ν f) - mconvL1E ν f = mconvL1E ν (transL1E y f - f) := by
    rw [ContinuousLinearMap.map_sub, mconvL1E_transL1E]
  rw [transDiffE, transDiffE, hcomm]
  exact norm_mconvL1E_le ν _

/-- **(★) after an operator**, with the bound still expressed at `f`.
@isnad1 id=le.0h4v.s14.67c4f0b35485 from=translated src=- shape=8f635a3c vocab=115a2ded
-/
theorem norm_mconvL1E_comp_sub_le (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : E →₁[volume] ℝ) :
    ‖mconvL1E μ (mconvL1E ν f) - mconvL1E ν f‖ ≤ ∫ y, transDiffE f y ∂μ :=
  (norm_mconvL1E_sub_le μ (mconvL1E ν f)).trans
    (integral_mono (integrable_transDiffE μ _) (integrable_transDiffE μ f)
      (transDiffE_mconvL1E_le ν f))

/-- The modulus of continuity as a bounded continuous function on `E`.-/
noncomputable def transDiffBCFE (f : E →₁[volume] ℝ) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (transDiffE f) (continuous_transDiffE f)
    (2 * ‖f‖) fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (transDiffE_nonneg f y)]
      exact transDiffE_le f y

/--
@isnad1 id=eq.0h3v.s8.12b745888674 from=translated src=- shape=0e0e6832 vocab=a74d2f37
-/
@[simp]
theorem transDiffBCFE_apply (f : E →₁[volume] ℝ) (y : E) :
    transDiffBCFE f y = transDiffE f y := rfl

/--
@isnad1 id=eq.0h2v.s7.8541286179d0 from=translated src=- shape=a35ea343 vocab=031846d9
-/
theorem transDiffE_real (f : X) (y : ℝ) : transDiffE f y = transDiff f y := by
  rw [transDiffE, transDiff, transL1E_real]

end Normed

/-! ## The Lévy clause, over an inner product space -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **Kernels whose characteristic functions tend to `1` concentrate at the origin**, measured by
the modulus of continuity.
@isnad1 id=tendsto.1h3v.s8.ae4d19ab17dc from=translated src=- shape=96f5d62b vocab=f4269a01
-/
theorem tendsto_integral_transDiffE_of_tendsto_charFun {μ : ℕ → Measure E}
    [hμ : ∀ n, IsProbabilityMeasure (μ n)]
    (h : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 1)) (f : E →₁[volume] ℝ) :
    Tendsto (fun n => ∫ y, transDiffE f y ∂(μ n)) atTop (𝓝 0) := by
  set P : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, hμ n⟩ with hP
  set P₀ : ProbabilityMeasure E := ⟨Measure.dirac 0, inferInstance⟩ with hP₀
  have hconv : Tendsto P atTop (𝓝 P₀) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun ω => ?_
    have h0 : charFun (P₀ : Measure E) ω = 1 := by
      change charFun (Measure.dirac (0 : E)) ω = 1
      rw [charFun_dirac]
      simp
    rw [h0]
    exact h ω
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv (transDiffBCFE f)
  simpa [hP, hP₀] using this

/-- **Kernels whose characteristic functions tend to `1` give operators tending strongly to the
identity.**
@isnad1 id=tendsto.1h3v.s12.70b5f6b983d4 from=translated src=- shape=44fa6369 vocab=f05acbd4
-/
theorem tendsto_norm_mconvL1E_sub_of_tendsto_charFun {μ : ℕ → Measure E}
    [∀ n, IsProbabilityMeasure (μ n)]
    (h : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 1)) (f : E →₁[volume] ℝ) :
    Tendsto (fun n => ‖mconvL1E (μ n) f - f‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_mconvL1E_sub_le (μ n) f)
    (tendsto_integral_transDiffE_of_tendsto_charFun h f)

end Inner

end ScaleSpace
