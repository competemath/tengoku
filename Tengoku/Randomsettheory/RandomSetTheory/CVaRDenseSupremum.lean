/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence
import Tengoku.Randomsettheory.RandomSetTheory.AtomlessDivisibility
import Tengoku.Randomsettheory.RandomSetTheory.DenseContinuousSupremum
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentMartingale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Passing finite maximal CVaR bounds to continuous index sets

The finite-supremum martingale bounds used in the polynomial branch are first
proved on finite prefixes of a countable dense family.  This file supplies the
missing analytic limit step.  Its main ingredients are an explicit `L¹`
Lipschitz estimate for conditional value at risk and dominated convergence for
dense prefix suprema.
-/

open Filter Real Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Conditional value at risk is `alpha⁻¹`-Lipschitz for the `L¹` distance.

This is proved directly from monotonicity, subadditivity and the variational
bound on a nonnegative loss, so it does not require a quantile representation.
@isnad1 id=le.4h5v.s7.fcfc5b5c8bc2 from=translated src=- shape=d5ac6185 vocab=67513624
-/
theorem abs_conditionalValueAtRisk_sub_le_integral_abs_sub
    [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Integrable X mu) (hY : Integrable Y mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    |conditionalValueAtRisk alpha X mu -
        conditionalValueAtRisk alpha Y mu| ≤
      alpha⁻¹ * ∫ omega, |X omega - Y omega| ∂mu := by
  let A : Omega → ℝ := fun omega ↦ |X omega - Y omega|
  have hA : Integrable A mu := (hX.sub hY).abs
  have hAnonneg : 0 ≤ᵐ[mu] A :=
    ae_of_all mu fun omega ↦ abs_nonneg (X omega - Y omega)
  have hAcvar : conditionalValueAtRisk alpha A mu ≤
      alpha⁻¹ * ∫ omega, A omega ∂mu :=
    conditionalValueAtRisk_le_inv_mul_integral_of_nonneg
      hA hAnonneg halpha0 halpha1
  have hXY : X ≤ᵐ[mu] fun omega ↦ Y omega + A omega := by
    filter_upwards [] with omega
    dsimp only [A]
    exact le_add_of_sub_left_le (le_abs_self (X omega - Y omega))
  have hYX : Y ≤ᵐ[mu] fun omega ↦ X omega + A omega := by
    filter_upwards [] with omega
    dsimp only [A]
    have h := neg_le_abs (X omega - Y omega)
    linarith
  have hYA : Integrable (fun omega ↦ Y omega + A omega) mu := hY.add hA
  have hXA : Integrable (fun omega ↦ X omega + A omega) mu := hX.add hA
  have hforward : conditionalValueAtRisk alpha X mu ≤
      conditionalValueAtRisk alpha Y mu +
        alpha⁻¹ * ∫ omega, A omega ∂mu := by
    calc
      conditionalValueAtRisk alpha X mu ≤
          conditionalValueAtRisk alpha (fun omega ↦ Y omega + A omega) mu :=
        conditionalValueAtRisk_mono_ae hX hYA halpha0 halpha1 hXY
      _ ≤ conditionalValueAtRisk alpha Y mu +
          conditionalValueAtRisk alpha A mu :=
        conditionalValueAtRisk_add_le hY hA halpha0 halpha1
      _ ≤ conditionalValueAtRisk alpha Y mu +
          alpha⁻¹ * ∫ omega, A omega ∂mu := add_le_add le_rfl hAcvar
  have hbackward : conditionalValueAtRisk alpha Y mu ≤
      conditionalValueAtRisk alpha X mu +
        alpha⁻¹ * ∫ omega, A omega ∂mu := by
    calc
      conditionalValueAtRisk alpha Y mu ≤
          conditionalValueAtRisk alpha (fun omega ↦ X omega + A omega) mu :=
        conditionalValueAtRisk_mono_ae hY hXA halpha0 halpha1 hYX
      _ ≤ conditionalValueAtRisk alpha X mu +
          conditionalValueAtRisk alpha A mu :=
        conditionalValueAtRisk_add_le hX hA halpha0 halpha1
      _ ≤ conditionalValueAtRisk alpha X mu +
          alpha⁻¹ * ∫ omega, A omega ∂mu := add_le_add le_rfl hAcvar
  rw [show (∫ omega, |X omega - Y omega| ∂mu) =
      ∫ omega, A omega ∂mu by rfl]
  rw [abs_le]
  constructor <;> linarith

/-- `L¹` convergence implies convergence of conditional value at risk at
every fixed tail mass.
@isnad1 id=tendsto.5h5v.s7.22b9fd90a954 from=translated src=- shape=3892b1a4 vocab=dd4fbe59
-/
theorem tendsto_conditionalValueAtRisk_of_tendsto_integral_abs_sub
    [IsProbabilityMeasure mu]
    {X : ℕ → Omega → ℝ} {Y : Omega → ℝ}
    (hX : ∀ n, Integrable (X n) mu) (hY : Integrable Y mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hL1 : Tendsto (fun n ↦ ∫ omega, |X n omega - Y omega| ∂mu)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ conditionalValueAtRisk alpha (X n) mu)
      atTop (nhds (conditionalValueAtRisk alpha Y mu)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ norm_nonneg _
  · exact Eventually.of_forall fun n ↦ by
      simpa only [Real.norm_eq_abs] using
        abs_conditionalValueAtRisk_sub_le_integral_abs_sub
          (hX n) hY halpha0 halpha1
  · simpa using (tendsto_const_nhds.mul hL1 :
      Tendsto
        (fun n ↦ alpha⁻¹ * ∫ omega, |X n omega - Y omega| ∂mu)
        atTop (nhds (alpha⁻¹ * 0)))

/-- Centering by the respective expectations costs at most a factor two in
`L¹`.  In particular, `L¹` convergence is preserved by centering.
@isnad1 id=tendsto.3h4v.s7.9b18a147fbff from=translated src=- shape=7f24e6d1 vocab=4edb6d6f
-/
theorem tendsto_integral_abs_centered_sub_centered
    [IsProbabilityMeasure mu]
    {X : ℕ → Omega → ℝ} {Y : Omega → ℝ}
    (hX : ∀ n, Integrable (X n) mu) (hY : Integrable Y mu)
    (hL1 : Tendsto (fun n ↦ ∫ omega, |X n omega - Y omega| ∂mu)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ ∫ omega,
        |(X n omega - ∫ z, X n z ∂mu) -
          (Y omega - ∫ z, Y z ∂mu)| ∂mu)
      atTop (nhds 0) := by
  let d : ℕ → ℝ := fun n ↦ ∫ omega, |X n omega - Y omega| ∂mu
  have hbound : ∀ n,
      (∫ omega,
          |(X n omega - ∫ z, X n z ∂mu) -
            (Y omega - ∫ z, Y z ∂mu)| ∂mu) ≤ 2 * d n := by
    intro n
    have hdiff : Integrable (fun omega ↦ |X n omega - Y omega|) mu :=
      ((hX n).sub hY).abs
    have hleft : Integrable (fun omega ↦
        |(X n omega - ∫ z, X n z ∂mu) -
          (Y omega - ∫ z, Y z ∂mu)|) mu :=
      (((hX n).sub (integrable_const _)).sub
        (hY.sub (integrable_const _))).abs
    have hright : Integrable (fun omega ↦
        |X n omega - Y omega| +
          |(∫ z, X n z ∂mu) - ∫ z, Y z ∂mu|) mu :=
      hdiff.add (integrable_const _)
    have hpoint : ∀ omega,
        |(X n omega - ∫ z, X n z ∂mu) -
            (Y omega - ∫ z, Y z ∂mu)| ≤
          |X n omega - Y omega| +
            |(∫ z, X n z ∂mu) - ∫ z, Y z ∂mu| := by
      intro omega
      rw [show
        (X n omega - ∫ z, X n z ∂mu) -
            (Y omega - ∫ z, Y z ∂mu) =
          (X n omega - Y omega) -
            ((∫ z, X n z ∂mu) - ∫ z, Y z ∂mu) by ring]
      exact abs_sub _ _
    have hint := integral_mono hleft hright hpoint
    rw [integral_add hdiff (integrable_const _), integral_const,
      probReal_univ, one_smul] at hint
    have hmean :
        |(∫ z, X n z ∂mu) - ∫ z, Y z ∂mu| ≤ d n := by
      rw [← integral_sub (hX n) hY]
      simpa only [Real.norm_eq_abs, d] using
        (norm_integral_le_integral_norm
          (μ := mu) (f := fun z ↦ X n z - Y z))
    exact hint.trans (by linarith)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _
  · exact Eventually.of_forall hbound
  · simpa only [d, mul_zero] using
      (tendsto_const_nhds.mul hL1 :
        Tendsto (fun n ↦ 2 * d n) atTop (nhds (2 * 0)))

/-- CVaR of the centered process is continuous under `L¹` convergence of the
uncentered process.
@isnad1 id=tendsto.5h5v.s7.a96b96bce6a9 from=translated src=- shape=9fa3af99 vocab=dd4fbe59
-/
theorem tendsto_conditionalValueAtRisk_centered_of_tendsto_integral_abs_sub
    [IsProbabilityMeasure mu]
    {X : ℕ → Omega → ℝ} {Y : Omega → ℝ}
    (hX : ∀ n, Integrable (X n) mu) (hY : Integrable Y mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hL1 : Tendsto (fun n ↦ ∫ omega, |X n omega - Y omega| ∂mu)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ conditionalValueAtRisk alpha
        (fun omega ↦ X n omega - ∫ z, X n z ∂mu) mu)
      atTop
      (nhds (conditionalValueAtRisk alpha
        (fun omega ↦ Y omega - ∫ z, Y z ∂mu) mu)) := by
  apply tendsto_conditionalValueAtRisk_of_tendsto_integral_abs_sub
    (fun n ↦ (hX n).sub (integrable_const _))
    (hY.sub (integrable_const _)) halpha0 halpha1
  exact tendsto_integral_abs_centered_sub_centered hX hY hL1

/-- On an atomless probability space, a CVaR upper bound implies the
corresponding strict upper-tail probability bound.

Atomlessness is used only to carve out an event of mass exactly `alpha` from
a hypothetical larger upper-tail event.  The eventwise dual inequality in
`CVaRQuantile` then gives the contradiction.
@isnad1 id=le.6h5v.s6.da226f112ae5 from=translated src=- shape=9a4a481b vocab=b73368d6
-/
theorem measureReal_lt_le_of_conditionalValueAtRisk_le_of_atomless
    [IsProbabilityMeasure mu]
    (hmu : RandomSetTheory.IsAtomlessMeasure mu)
    {X : Omega → ℝ} (hXmeas : Measurable X) (hX : Integrable X mu)
    {alpha C : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hcvar : conditionalValueAtRisk alpha X mu ≤ C) :
    mu.real {omega | C < X omega} ≤ alpha := by
  let U : Set Omega := {omega | C < X omega}
  have hU : MeasurableSet U := hXmeas measurableSet_Ioi
  by_contra htail
  have halphaU : alpha < mu.real U := lt_of_not_ge htail
  obtain ⟨A, hAU, hAmeas, hAmeasure⟩ :=
    hmu.exists_subset_measureReal_eq hU halpha0.le halphaU.le
  have hArealPos : 0 < mu.real A := by simpa only [hAmeasure] using halpha0
  have hApos : 0 < mu A := (ENNReal.toReal_pos_iff.mp hArealPos).1
  let G : Omega → ℝ := A.indicator fun omega ↦ X omega - C
  have hGint : Integrable G mu :=
    (hX.sub (integrable_const C)).indicator hAmeas
  have hGnonneg : (fun _ : Omega ↦ (0 : ℝ)) ≤ᵐ[mu] G := by
    exact ae_of_all mu fun omega ↦ by
      by_cases homega : omega ∈ A
      · rw [show G omega = X omega - C by
          simp only [G, Set.indicator_of_mem homega]]
        have hstrict := hAU homega
        change C < X omega at hstrict
        linarith
      · simp only [G, Set.indicator_of_notMem homega, le_refl]
  have hAsupport : A ⊆ Function.support G := by
    intro omega homega
    have hstrict := hAU homega
    change C < X omega at hstrict
    change G omega ≠ 0
    simp only [G, Set.indicator_of_mem homega]
    linarith
  have hsupport : 0 < mu (Function.support G) :=
    hApos.trans_le (measure_mono hAsupport)
  have hGpos : 0 < ∫ omega, G omega ∂mu :=
    (integral_pos_iff_support_of_nonneg_ae hGnonneg hGint).2 hsupport
  have hstrictIntegral : alpha * C < ∫ omega in A, X omega ∂mu := by
    dsimp only [G] at hGpos
    rw [integral_indicator hAmeas,
      integral_sub hX.integrableOn (integrable_const C),
      setIntegral_const, smul_eq_mul, hAmeasure] at hGpos
    linarith
  have hevent :=
    setIntegral_le_mul_conditionalValueAtRisk_of_measureReal_eq
      hX hAmeas halpha0 halpha1 hAmeasure
  have hscaled : alpha * conditionalValueAtRisk alpha X mu ≤ alpha * C :=
    mul_le_mul_of_nonneg_left hcvar halpha0.le
  linarith

end ProbabilityTheory

namespace RandomSetTheory

variable {Omega T : Type*}
variable [MeasurableSpace Omega]
variable [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
variable {mu : Measure Omega}

/-- The full supremum of a continuous process is measurable when all
evaluations on the canonical dense sequence are measurable.
@isnad1 id=measurab.2h3v.s6.49d3ed675388 from=translated src=- shape=ae68e5e4 vocab=1fac94cf
-/
theorem measurable_iSup_continuous_of_measurable_dense
    (F : Omega → T → ℝ) (hcontinuous : ∀ omega, Continuous (F omega))
    (hmeas : ∀ k, Measurable (fun omega ↦ F omega (denseSeq T k))) :
    Measurable (fun omega ↦ ⨆ t, F omega t) := by
  have hdense : (fun omega ↦ ⨆ k : ℕ, F omega (denseSeq T k)) =
      fun omega ↦ ⨆ t, F omega t := by
    funext omega
    exact iSup_denseSeq_eq_iSup (F omega) (hcontinuous omega)
  rw [← hdense]
  exact Measurable.iSup hmeas

/-- Dense prefix suprema converge in `L¹` to the full supremum under one
integrable pathwise envelope.
@isnad1 id=tendsto.4h5v.s7.952d12fda777 from=translated src=- shape=0ed3421d vocab=f02337bb
-/
theorem tendsto_integral_abs_densePrefixSupremum_sub_iSup
    (F : Omega → T → ℝ) (B : Omega → ℝ)
    (hcontinuous : ∀ omega, Continuous (F omega))
    (hmeas : ∀ k, Measurable (fun omega ↦ F omega (denseSeq T k)))
    (hB : Integrable B mu)
    (hdom : ∀ omega t, |F omega t| ≤ |B omega|) :
    Tendsto
      (fun n ↦ ∫ omega,
        |densePrefixSupremum (F omega) n - (⨆ t, F omega t)| ∂mu)
      atTop (nhds 0) := by
  let P : ℕ → Omega → ℝ := fun n omega ↦ densePrefixSupremum (F omega) n
  let S : Omega → ℝ := fun omega ↦ ⨆ t, F omega t
  have hPmeas : ∀ n, Measurable (P n) := fun n ↦
    measurable_densePrefixSupremum F hmeas n
  have hSmeas : Measurable S :=
    measurable_iSup_continuous_of_measurable_dense F hcontinuous hmeas
  have hPdom : ∀ n omega, |P n omega| ≤ |B omega| := by
    intro n omega
    have heq : P n omega = ProbabilityTheory.finiteProcessSupremum
        (Finset.range (n + 1)) Finset.nonempty_range_add_one
          (fun k omega ↦ F omega (denseSeq T k)) omega := by
      dsimp only [P, ProbabilityTheory.finiteProcessSupremum]
      exact densePrefixSupremum_eq_sup'_range _ n
    rw [heq]
    apply ProbabilityTheory.abs_finiteProcessSupremum_le
      (Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun k omega ↦ F omega (denseSeq T k)) B
    · intro omega' k _hk
      exact hdom omega' (denseSeq T k)
  have hSdom : ∀ omega, |S omega| ≤ |B omega| := by
    intro omega
    have hbdd : BddAbove (Set.range (F omega)) := by
      refine ⟨|B omega|, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact (le_abs_self (F omega t)).trans (hdom omega t)
    have hupper : S omega ≤ |B omega| := by
      exact ciSup_le fun t ↦ (le_abs_self (F omega t)).trans (hdom omega t)
    let t0 : T := Classical.choice inferInstance
    have hlowerValue : -|B omega| ≤ F omega t0 := by
      exact (neg_le_neg (hdom omega t0)).trans (neg_abs_le (F omega t0))
    have hlower : -|B omega| ≤ S omega :=
      hlowerValue.trans (le_ciSup hbdd t0)
    exact (abs_le).2 ⟨hlower, hupper⟩
  have hpoint : ∀ omega, Tendsto (fun n ↦ P n omega) atTop (nhds (S omega)) := by
    intro omega
    apply tendsto_densePrefixSupremum (F omega) (hcontinuous omega)
    refine ⟨|B omega|, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (le_abs_self (F omega t)).trans (hdom omega t)
  have hdiffMeas : ∀ n, AEStronglyMeasurable
      (fun omega ↦ |P n omega - S omega|) mu := fun n ↦
    ((hPmeas n).sub hSmeas).abs.aestronglyMeasurable
  have hboundInt : Integrable (fun omega ↦ 2 * |B omega|) mu :=
    hB.abs.const_mul 2
  have hdiffBound : ∀ n, ∀ᵐ omega ∂mu,
      ‖|P n omega - S omega|‖ ≤ 2 * |B omega| := by
    intro n
    exact ae_of_all mu fun omega ↦ by
      rw [Real.norm_eq_abs, abs_abs]
      calc
        |P n omega - S omega| ≤ |P n omega| + |S omega| := abs_sub _ _
        _ ≤ |B omega| + |B omega| := add_le_add (hPdom n omega) (hSdom omega)
        _ = 2 * |B omega| := by ring
  have hdiffTendsto : ∀ᵐ omega ∂mu,
      Tendsto (fun n ↦ |P n omega - S omega|) atTop (nhds 0) := by
    exact ae_of_all mu fun omega ↦ by
      have hsub : Tendsto (fun n ↦ P n omega - S omega)
          atTop (nhds 0) := by
        simpa using (hpoint omega).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ S omega)
            atTop (nhds (S omega)))
      simpa only [Function.comp_def, abs_zero] using
        (continuous_abs.tendsto 0).comp hsub
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun omega ↦ 2 * |B omega|) hdiffMeas hboundInt hdiffBound hdiffTendsto
  simpa only [P, S, integral_zero] using hDCT

/-- The centered CVaR of dense finite prefix suprema converges to that of the
full continuous supremum.  This is the finite-to-continuous bridge needed by
maximal inequalities proved first for a finite index class.
@isnad1 id=tendsto.6h6v.s8.5eccc36108b5 from=translated src=- shape=943c6827 vocab=42ce490f
-/
theorem tendsto_conditionalValueAtRisk_centered_densePrefixSupremum
    [IsProbabilityMeasure mu]
    (F : Omega → T → ℝ) (B : Omega → ℝ)
    (hcontinuous : ∀ omega, Continuous (F omega))
    (hmeas : ∀ k, Measurable (fun omega ↦ F omega (denseSeq T k)))
    (hB : Integrable B mu)
    (hdom : ∀ omega t, |F omega t| ≤ |B omega|)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    Tendsto
      (fun n ↦ ProbabilityTheory.conditionalValueAtRisk alpha
        (fun omega ↦
          densePrefixSupremum (F omega) n -
            ∫ z, densePrefixSupremum (F z) n ∂mu) mu)
      atTop
      (nhds (ProbabilityTheory.conditionalValueAtRisk alpha
        (fun omega ↦
          (⨆ t, F omega t) - ∫ z, (⨆ t, F z t) ∂mu) mu)) := by
  let P : ℕ → Omega → ℝ := fun n omega ↦ densePrefixSupremum (F omega) n
  let S : Omega → ℝ := fun omega ↦ ⨆ t, F omega t
  have hPmeas : ∀ n, Measurable (P n) := fun n ↦
    measurable_densePrefixSupremum F hmeas n
  have hSmeas : Measurable S :=
    measurable_iSup_continuous_of_measurable_dense F hcontinuous hmeas
  have hPdom : ∀ n omega, |P n omega| ≤ |B omega| := by
    intro n omega
    have heq : P n omega = ProbabilityTheory.finiteProcessSupremum
        (Finset.range (n + 1)) Finset.nonempty_range_add_one
          (fun k omega ↦ F omega (denseSeq T k)) omega := by
      dsimp only [P, ProbabilityTheory.finiteProcessSupremum]
      exact densePrefixSupremum_eq_sup'_range _ n
    rw [heq]
    apply ProbabilityTheory.abs_finiteProcessSupremum_le
      (Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun k omega ↦ F omega (denseSeq T k)) B
    · intro omega' k _hk
      exact hdom omega' (denseSeq T k)
  have hSdom : ∀ omega, |S omega| ≤ |B omega| := by
    intro omega
    have hbdd : BddAbove (Set.range (F omega)) := by
      refine ⟨|B omega|, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact (le_abs_self (F omega t)).trans (hdom omega t)
    have hupper : S omega ≤ |B omega| :=
      ciSup_le fun t ↦ (le_abs_self (F omega t)).trans (hdom omega t)
    let t0 : T := Classical.choice inferInstance
    have hlowerValue : -|B omega| ≤ F omega t0 :=
      (neg_le_neg (hdom omega t0)).trans (neg_abs_le (F omega t0))
    have hlower : -|B omega| ≤ S omega :=
      hlowerValue.trans (le_ciSup hbdd t0)
    exact (abs_le).2 ⟨hlower, hupper⟩
  have hPint : ∀ n, Integrable (P n) mu := by
    intro n
    apply hB.norm.mono' (hPmeas n).aestronglyMeasurable
    exact ae_of_all mu fun omega ↦ by
      simpa only [Real.norm_eq_abs, abs_abs] using hPdom n omega
  have hSint : Integrable S mu := by
    apply hB.norm.mono' hSmeas.aestronglyMeasurable
    exact ae_of_all mu fun omega ↦ by
      simpa only [Real.norm_eq_abs, abs_abs] using hSdom omega
  have hL1 : Tendsto (fun n ↦ ∫ omega, |P n omega - S omega| ∂mu)
      atTop (nhds 0) := by
    simpa only [P, S] using
      tendsto_integral_abs_densePrefixSupremum_sub_iSup
        F B hcontinuous hmeas hB hdom
  simpa only [P, S] using
    (ProbabilityTheory.tendsto_conditionalValueAtRisk_centered_of_tendsto_integral_abs_sub
        hPint hSint halpha0 halpha1 hL1)

/-- Any uniform CVaR bound for all dense finite prefix suprema passes without
loss to the supremum over the entire continuous index space.
@isnad1 id=le.7h7v.s8.a0027be3f0a5 from=translated src=- shape=0d33c8a6 vocab=aea3f510
-/
theorem conditionalValueAtRisk_centered_iSup_le_of_densePrefixes
    [IsProbabilityMeasure mu]
    (F : Omega → T → ℝ) (B : Omega → ℝ)
    (hcontinuous : ∀ omega, Continuous (F omega))
    (hmeas : ∀ k, Measurable (fun omega ↦ F omega (denseSeq T k)))
    (hB : Integrable B mu)
    (hdom : ∀ omega t, |F omega t| ≤ |B omega|)
    {alpha C : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hfinite : ∀ n,
      ProbabilityTheory.conditionalValueAtRisk alpha
        (fun omega ↦
          densePrefixSupremum (F omega) n -
            ∫ z, densePrefixSupremum (F z) n ∂mu) mu ≤ C) :
    ProbabilityTheory.conditionalValueAtRisk alpha
        (fun omega ↦
          (⨆ t, F omega t) - ∫ z, (⨆ t, F z t) ∂mu) mu ≤ C := by
  exact le_of_tendsto
    (tendsto_conditionalValueAtRisk_centered_densePrefixSupremum
      F B hcontinuous hmeas hB hdom halpha0 halpha1)
    (Eventually.of_forall hfinite)

/-- Uniform finite-prefix CVaR estimates yield the corresponding strict-tail
bound for the full continuous supremum on an atomless probability space.
@isnad1 id=le.8h7v.s8.b220d88919c3 from=translated src=- shape=70a3a725 vocab=88863526
-/
theorem measureReal_centered_iSup_lt_le_of_densePrefixes
    [IsProbabilityMeasure mu]
    (hmu : IsAtomlessMeasure mu)
    (F : Omega → T → ℝ) (B : Omega → ℝ)
    (hcontinuous : ∀ omega, Continuous (F omega))
    (hmeas : ∀ k, Measurable (fun omega ↦ F omega (denseSeq T k)))
    (hB : Integrable B mu)
    (hdom : ∀ omega t, |F omega t| ≤ |B omega|)
    {alpha C : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hfinite : ∀ n,
      ProbabilityTheory.conditionalValueAtRisk alpha
        (fun omega ↦
          densePrefixSupremum (F omega) n -
            ∫ z, densePrefixSupremum (F z) n ∂mu) mu ≤ C) :
    mu.real {omega |
      C < (⨆ t, F omega t) - ∫ z, (⨆ t, F z t) ∂mu} ≤ alpha := by
  let S : Omega → ℝ := fun omega ↦ ⨆ t, F omega t
  have hSmeas : Measurable S :=
    measurable_iSup_continuous_of_measurable_dense F hcontinuous hmeas
  have hSdom : ∀ omega, |S omega| ≤ |B omega| := by
    intro omega
    have hbdd : BddAbove (Set.range (F omega)) := by
      refine ⟨|B omega|, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact (le_abs_self (F omega t)).trans (hdom omega t)
    have hupper : S omega ≤ |B omega| :=
      ciSup_le fun t ↦ (le_abs_self (F omega t)).trans (hdom omega t)
    let t0 : T := Classical.choice inferInstance
    have hlowerValue : -|B omega| ≤ F omega t0 :=
      (neg_le_neg (hdom omega t0)).trans (neg_abs_le (F omega t0))
    have hlower : -|B omega| ≤ S omega :=
      hlowerValue.trans (le_ciSup hbdd t0)
    exact (abs_le).2 ⟨hlower, hupper⟩
  have hSint : Integrable S mu := by
    apply hB.norm.mono' hSmeas.aestronglyMeasurable
    exact ae_of_all mu fun omega ↦ by
      simpa only [Real.norm_eq_abs, abs_abs] using hSdom omega
  have hcenteredMeas : Measurable
      (fun omega ↦ S omega - ∫ z, S z ∂mu) := hSmeas.sub measurable_const
  have hcenteredInt : Integrable
      (fun omega ↦ S omega - ∫ z, S z ∂mu) mu :=
    hSint.sub (integrable_const _)
  have hcvar : ProbabilityTheory.conditionalValueAtRisk alpha
      (fun omega ↦ S omega - ∫ z, S z ∂mu) mu ≤ C := by
    simpa only [S] using
      conditionalValueAtRisk_centered_iSup_le_of_densePrefixes
        F B hcontinuous hmeas hB hdom halpha0 halpha1 hfinite
  simpa only [S] using
    (ProbabilityTheory.measureReal_lt_le_of_conditionalValueAtRisk_le_of_atomless
        hmu hcenteredMeas hcenteredInt halpha0 halpha1 hcvar)

end RandomSetTheory
