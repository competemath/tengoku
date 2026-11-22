/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.BoundedInProbability
import Tengoku.Randomsettheory.RandomSetTheory.ZeroSetStability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Functional weak convergence and oracle zero-set rates

This file isolates the final probabilistic transfer used by the oracle
zero-set result.  The difficult functional central limit theorem is an
explicit premise: if the already root-`n` scaled full support process
converges in distribution in a normed process space, then it is bounded in
probability.  A deterministic comparison between its norm and the uniform
Hausdorff error gives `sqrt n * Δₙ = O_P(1)`, and the metric error bound then
transfers this rate to the enlarged zero set.

The process space can in particular be a space of continuous functions with
the uniform norm.  No Donsker theorem or tightness argument is claimed here.
-/

open Set Metric Filter MeasureTheory

noncomputable section

namespace RandomSetTheory

/-- A functional weak limit for an already root-`n` scaled process implies
root-`n` boundedness in probability of any nonnegative uniform error that is
deterministically dominated by the process norm.

In the intended application, `X n ω` is the full scaled support-difference
process and `Δ n ω` is the parameter-uniform Hausdorff error.  Thus `hlink`
is precisely the deterministic support/Hausdorff comparison that connects
the functional CLT to the set-valued estimation error.
@isnad1 id=isbounde.3h8v.s7.9063535fd584 from=translated src=- shape=1a8f184c vocab=c9c31b30
-/
theorem rootN_uniformError_isBoundedInProbability_of_processCLT
    {Ω Ω' F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace F] [NormedAddCommGroup F] [BorelSpace F]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (mu' : Measure Ω') [IsProbabilityMeasure mu']
    (X : ℕ → Ω → F) (Z : Ω' → F) (Δ : ℕ → Ω → ℝ)
    (hΔ : ∀ n ω, 0 ≤ Δ n ω)
    (hprocess : TendstoInDistribution X atTop Z (fun _ ↦ mu) mu')
    (hlink : ∀ (n : ℕ) (ω : Ω),
      Real.sqrt (n : ℝ) * Δ n ω ≤ ‖X n ω‖) :
    IsBoundedInProbability mu atTop
      (fun (n : ℕ) ω ↦ Real.sqrt (n : ℝ) * Δ n ω) := by
  have hnorm : TendstoInDistribution
      (fun n ↦ (fun f : F ↦ ‖f‖) ∘ X n) atTop
      ((fun f : F ↦ ‖f‖) ∘ Z) (fun _ ↦ mu) mu' :=
    hprocess.continuous_comp continuous_norm
  apply hnorm.isBoundedInProbability.mono_norm (c := 1) zero_le_one
  filter_upwards [] with n
  intro ω
  simp only [Function.comp_apply, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (hΔ n ω)),
    abs_of_nonneg (norm_nonneg (X n ω))]
  exact hlink n ω

/-- Functional-CLT-to-oracle-rate bridge.  Weak convergence of the full
root-`n` scaled process, together with the explicit deterministic domination
of the uniform Hausdorff error by its norm, implies root-`n` boundedness in
probability of the oracle enlarged-zero-set Hausdorff error.
@isnad1 id=isbounde.7h13v.s8.58407a81662e from=translated src=- shape=e5855ad7 vocab=c1fb9d26
-/
theorem rootN_enlargedZeroSet_of_processCLT
    {Ω Ω' Θ E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace Θ] [SeminormedAddCommGroup E]
    [MeasurableSpace F] [NormedAddCommGroup F] [BorelSpace F]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (mu' : Measure Ω') [IsProbabilityMeasure mu']
    (X : ℕ → Ω → F) (Z : Ω' → F)
    (Ghat : ℕ → Ω → Θ → Set E) (G : Θ → Set E)
    (Δ : ℕ → Ω → ℝ) {κ : ℝ}
    (hΔ : ∀ n ω, 0 ≤ Δ n ω)
    (hprocess : TendstoInDistribution X atTop Z (fun _ ↦ mu) mu')
    (hlink : ∀ (n : ℕ) (ω : Ω),
      Real.sqrt (n : ℝ) * Δ n ω ≤ ‖X n ω‖)
    (hκ : 0 < κ)
    (hfin : ∀ n ω θ, hausdorffEDist (Ghat n ω θ) (G θ) ≠ ⊤)
    (hhaus : ∀ n ω θ,
      hausdorffDist (Ghat n ω θ) (G θ) ≤ Δ n ω)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ)) :
    IsBoundedInProbability mu atTop (fun (n : ℕ) ω ↦
      Real.sqrt (n : ℝ) * hausdorffDist
        (enlargedSetValuedZeroSet (Ghat n ω) (Δ n ω))
        (setValuedZeroSet G)) := by
  apply rootN_enlargedZeroSet_of_rootN_uniformHausdorff
    mu Ghat G Δ hΔ hκ hfin hhaus herror
  exact rootN_uniformError_isBoundedInProbability_of_processCLT
    mu mu' X Z Δ hΔ hprocess hlink

end RandomSetTheory
