/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.BoundedInProbability
import Tengoku.Randomsettheory.RandomSetTheory.Geometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stability of zero sets of set-valued maps

Uniform Hausdorff control of a set-valued estimating equation controls its
minimum-norm criterion.  Under a metric error bound for the population map,
the corresponding enlarged empirical zero set lies within `2 * Δ / κ` of
the population zero set.  This is the deterministic core of the oracle
zero-set result in Section 5 of the report.
-/

open Set Metric Filter Topology MeasureTheory

noncomputable section

namespace RandomSetTheory

/-- Exact zero set of a set-valued map.-/
def setValuedZeroSet
    {Θ E : Type*} [Zero E] (G : Θ → Set E) : Set Θ :=
  {θ | 0 ∈ G θ}

/-- `Δ`-enlarged zero set defined by the minimum distance to zero.-/
def enlargedSetValuedZeroSet
    {Θ E : Type*} [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) (Δ : ℝ) : Set Θ :=
  {θ | infDist 0 (G θ) ≤ Δ}

/-- A uniform Hausdorff bound puts every exact population zero in the
corresponding enlarged empirical zero set.-/
theorem setValuedZeroSet_subset_enlarged
    {Θ E : Type*} [SeminormedAddCommGroup E]
    (Ghat G : Θ → Set E) {Δ : ℝ}
    (hfin : ∀ θ, hausdorffEDist (Ghat θ) (G θ) ≠ ⊤)
    (hhaus : ∀ θ, hausdorffDist (Ghat θ) (G θ) ≤ Δ) :
    setValuedZeroSet G ⊆ enlargedSetValuedZeroSet Ghat Δ := by
  intro θ hθ
  have hGzero : infDist 0 (G θ) = 0 := infDist_zero_of_mem hθ
  have hstab := abs_infDist_zero_sub_infDist_zero_le_hausdorffDist
    (Ghat θ) (G θ) (hfin θ)
  change infDist 0 (Ghat θ) ≤ Δ
  calc
    infDist 0 (Ghat θ) =
        |infDist 0 (Ghat θ) - infDist 0 (G θ)| := by
      rw [hGzero, sub_zero, abs_of_nonneg infDist_nonneg]
    _ ≤ hausdorffDist (Ghat θ) (G θ) := hstab
    _ ≤ Δ := hhaus θ

/-- A version with distinct approximation error `δ` and enlargement
threshold `τ`.  Population zeros are retained as soon as `δ ≤ τ`.-/
theorem setValuedZeroSet_subset_enlarged_of_le
    {Θ E : Type*} [SeminormedAddCommGroup E]
    (Ghat G : Θ → Set E) {δ τ : ℝ} (hδτ : δ ≤ τ)
    (hfin : ∀ θ, hausdorffEDist (Ghat θ) (G θ) ≠ ⊤)
    (hhaus : ∀ θ, hausdorffDist (Ghat θ) (G θ) ≤ δ) :
    setValuedZeroSet G ⊆ enlargedSetValuedZeroSet Ghat τ := by
  intro θ hθ
  exact (setValuedZeroSet_subset_enlarged Ghat G hfin hhaus hθ).trans hδτ

/-- General thresholded oracle bound.  If the empirical correspondence is
within `δ` of the population correspondence and the retained threshold is
`τ ≥ δ`, the zero-set error is at most `(τ + δ) / κ`.-/
theorem hausdorffDist_enlargedSetValuedZeroSet_le_add
    {Θ E : Type*} [PseudoMetricSpace Θ] [SeminormedAddCommGroup E]
    (Ghat G : Θ → Set E) {δ τ κ : ℝ}
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hδτ : δ ≤ τ) (hκ : 0 < κ)
    (hfin : ∀ θ, hausdorffEDist (Ghat θ) (G θ) ≠ ⊤)
    (hhaus : ∀ θ, hausdorffDist (Ghat θ) (G θ) ≤ δ)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ)) :
    hausdorffDist (enlargedSetValuedZeroSet Ghat τ)
        (setValuedZeroSet G) ≤ (τ + δ) / κ := by
  have hsubset : setValuedZeroSet G ⊆ enlargedSetValuedZeroSet Ghat τ :=
    setValuedZeroSet_subset_enlarged_of_le Ghat G hδτ hfin hhaus
  apply hausdorffDist_le_of_infDist (div_nonneg (add_nonneg hτ hδ) hκ.le)
  · intro θ hθ
    have hstab := abs_infDist_zero_sub_infDist_zero_le_hausdorffDist
      (G θ) (Ghat θ) (by
        simpa [hausdorffEDist_comm] using hfin θ)
    have hdiff : infDist 0 (G θ) - infDist 0 (Ghat θ) ≤ δ :=
      (le_abs_self _).trans (hstab.trans (by
        simpa [hausdorffDist_comm] using hhaus θ))
    have hGhat : infDist 0 (Ghat θ) ≤ τ := hθ
    have hG : infDist 0 (G θ) ≤ τ + δ := by linarith
    apply (le_div_iff₀ hκ).2
    simpa [mul_comm] using (herror θ).trans hG
  · intro θ hθ
    exact (infDist_zero_of_mem (hsubset hθ)).le.trans
      (div_nonneg (add_nonneg hτ hδ) hκ.le)

/-- Oracle enlarged-zero-set bound.  If the population minimum-distance
criterion dominates `κ` times distance to its exact zero set, uniform
Hausdorff error `Δ` yields the sharp deterministic factor `2 * Δ / κ`.-/
theorem hausdorffDist_enlargedSetValuedZeroSet_le
    {Θ E : Type*} [PseudoMetricSpace Θ] [SeminormedAddCommGroup E]
    (Ghat G : Θ → Set E) {Δ κ : ℝ}
    (hΔ : 0 ≤ Δ) (hκ : 0 < κ)
    (hfin : ∀ θ, hausdorffEDist (Ghat θ) (G θ) ≠ ⊤)
    (hhaus : ∀ θ, hausdorffDist (Ghat θ) (G θ) ≤ Δ)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ)) :
    hausdorffDist (enlargedSetValuedZeroSet Ghat Δ)
        (setValuedZeroSet G) ≤ 2 * Δ / κ := by
  simpa [two_mul] using
    hausdorffDist_enlargedSetValuedZeroSet_le_add Ghat G
      hΔ hΔ le_rfl hκ hfin hhaus herror

/-- Filter-level consistency corollary of the oracle bound.  In particular,
any deterministic, almost-sure, or conditional path along which the uniform
Hausdorff error tends to zero yields convergence of the enlarged zero set.-/
theorem tendsto_hausdorffDist_enlargedSetValuedZeroSet
    {Θ E ι : Type*} [PseudoMetricSpace Θ] [SeminormedAddCommGroup E]
    {l : Filter ι} (Ghat : ι → Θ → Set E) (G : Θ → Set E)
    (Δ : ι → ℝ) {κ : ℝ}
    (hΔ : ∀ i, 0 ≤ Δ i) (hκ : 0 < κ)
    (hfin : ∀ i θ, hausdorffEDist (Ghat i θ) (G θ) ≠ ⊤)
    (hhaus : ∀ i θ, hausdorffDist (Ghat i θ) (G θ) ≤ Δ i)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ))
    (hΔzero : Tendsto Δ l (nhds 0)) :
    Tendsto
      (fun i => hausdorffDist
        (enlargedSetValuedZeroSet (Ghat i) (Δ i))
        (setValuedZeroSet G)) l (nhds 0) := by
  apply squeeze_zero
    (fun _ => hausdorffDist_nonneg)
    (fun i => hausdorffDist_enlargedSetValuedZeroSet_le
      (Ghat i) G (hΔ i) hκ (hfin i) (hhaus i) herror)
  simpa using (hΔzero.const_mul 2).div_const κ

/-- Failure of the oracle zero-set bound can only occur if the underlying
correspondence error exceeds the prescribed uniform threshold somewhere in
the parameter space.-/
theorem enlargedZeroSet_failure_subset_uniformHausdorff_failure
    {Ω Θ E : Type*} [PseudoMetricSpace Θ] [SeminormedAddCommGroup E]
    (Ghat : Ω → Θ → Set E) (G : Θ → Set E) {δ κ : ℝ}
    (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hfin : ∀ ω θ, hausdorffEDist (Ghat ω θ) (G θ) ≠ ⊤)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ)) :
    {ω | 2 * δ / κ < hausdorffDist
        (enlargedSetValuedZeroSet (Ghat ω) δ) (setValuedZeroSet G)} ⊆
      {ω | ∃ θ, δ < hausdorffDist (Ghat ω θ) (G θ)} := by
  intro ω hω
  by_contra hgood
  have hhaus : ∀ θ, hausdorffDist (Ghat ω θ) (G θ) ≤ δ := by
    intro θ
    exact le_of_not_gt (fun hbad => hgood ⟨θ, hbad⟩)
  exact (not_lt_of_ge
    (hausdorffDist_enlargedSetValuedZeroSet_le
      (Ghat ω) G hδ hκ (hfin ω) hhaus herror)) hω

/-- Probability/outer-measure transfer associated with the previous event
inclusion.  No measurability assumption on an uncountable parameter supremum
is hidden in the statement.-/
theorem measure_enlargedZeroSet_failure_le_uniformHausdorff_failure
    {Ω Θ E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [SeminormedAddCommGroup E]
    (μ : Measure Ω) (Ghat : Ω → Θ → Set E) (G : Θ → Set E) {δ κ : ℝ}
    (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hfin : ∀ ω θ, hausdorffEDist (Ghat ω θ) (G θ) ≠ ⊤)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ)) :
    μ {ω | 2 * δ / κ < hausdorffDist
        (enlargedSetValuedZeroSet (Ghat ω) δ) (setValuedZeroSet G)} ≤
      μ {ω | ∃ θ, δ < hausdorffDist (Ghat ω θ) (G θ)} :=
  measure_mono
    (enlargedZeroSet_failure_subset_uniformHausdorff_failure
      Ghat G hδ hκ hfin herror)

/-! ## Probabilistic rate transfer -/

/-- Any stochastic boundedness rate for the uniform correspondence error is
inherited by the oracle enlarged zero set.  Taking `r n = sqrt n` is the
formal `O_P(n⁻¹/²)` conclusion; no functional CLT is assumed or hidden here.-/
theorem isBoundedInProbability_scaled_enlargedZeroSet
    {Ω Θ E ι : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [SeminormedAddCommGroup E]
    (μ : Measure Ω) {l : Filter ι}
    (Ghat : ι → Ω → Θ → Set E) (G : Θ → Set E)
    (Δ r : ι → Ω → ℝ) {κ : ℝ}
    (hΔ : ∀ i ω, 0 ≤ Δ i ω) (hr : ∀ i ω, 0 ≤ r i ω)
    (hκ : 0 < κ)
    (hfin : ∀ i ω θ, hausdorffEDist (Ghat i ω θ) (G θ) ≠ ⊤)
    (hhaus : ∀ i ω θ,
      hausdorffDist (Ghat i ω θ) (G θ) ≤ Δ i ω)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ))
    (hbounded : IsBoundedInProbability μ l
      (fun i ω => r i ω * Δ i ω)) :
    IsBoundedInProbability μ l (fun i ω =>
      r i ω * hausdorffDist
        (enlargedSetValuedZeroSet (Ghat i ω) (Δ i ω))
        (setValuedZeroSet G)) := by
  apply hbounded.mono_norm (c := 2 / κ) (div_nonneg (by norm_num) hκ.le)
  filter_upwards [] with i
  intro ω
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (hr i ω) hausdorffDist_nonneg),
    abs_of_nonneg (mul_nonneg (hr i ω) (hΔ i ω))]
  calc
    r i ω * hausdorffDist
        (enlargedSetValuedZeroSet (Ghat i ω) (Δ i ω))
        (setValuedZeroSet G) ≤
      r i ω * (2 * Δ i ω / κ) :=
        mul_le_mul_of_nonneg_left
          (hausdorffDist_enlargedSetValuedZeroSet_le
            (Ghat i ω) G (hΔ i ω) hκ (hfin i ω)
              (hhaus i ω) herror)
          (hr i ω)
    _ = (2 / κ) * (r i ω * Δ i ω) := by ring

/-- Root-`n` specialization of
`isBoundedInProbability_scaled_enlargedZeroSet`.  Thus the exact conclusion
of the oracle corollary follows as soon as the uniform Hausdorff error is
root-`n` bounded in probability.-/
theorem rootN_enlargedZeroSet_of_rootN_uniformHausdorff
    {Ω Θ E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [SeminormedAddCommGroup E]
    (μ : Measure Ω) (Ghat : ℕ → Ω → Θ → Set E) (G : Θ → Set E)
    (Δ : ℕ → Ω → ℝ) {κ : ℝ}
    (hΔ : ∀ n ω, 0 ≤ Δ n ω) (hκ : 0 < κ)
    (hfin : ∀ n ω θ, hausdorffEDist (Ghat n ω θ) (G θ) ≠ ⊤)
    (hhaus : ∀ n ω θ,
      hausdorffDist (Ghat n ω θ) (G θ) ≤ Δ n ω)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ))
    (hrootN : IsBoundedInProbability μ atTop
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) * Δ n ω)) :
    IsBoundedInProbability μ atTop (fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) * hausdorffDist
        (enlargedSetValuedZeroSet (Ghat n ω) (Δ n ω))
        (setValuedZeroSet G)) := by
  exact isBoundedInProbability_scaled_enlargedZeroSet μ Ghat G Δ
    (fun (n : ℕ) (_ : Ω) => Real.sqrt (n : ℝ)) hΔ
    (fun n _ => Real.sqrt_nonneg (n : ℝ))
    hκ hfin hhaus herror hrootN

end RandomSetTheory
