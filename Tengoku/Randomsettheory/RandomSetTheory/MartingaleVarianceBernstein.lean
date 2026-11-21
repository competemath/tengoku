/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.MartingaleTruncation
import Tengoku.Randomsettheory.RandomSetTheory.BoundedVarianceBernstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Variance-sensitive Bernstein inequalities for martingale differences

This file supplies the variance-sensitive replacement for the elementary
Azuma step in `MartingaleTruncation`.  The central notion is a conditional
Bernstein MGF bound.  Unlike an independence certificate, it is designed to
compose along a filtration: if the partial sum is measurable at the current
filtration level, the conditional MGF bound for the next difference can be
pulled through the conditional expectation.

The final statements use deterministic upper bounds `v k` for the conditional
second moments.  Their variance proxies add, while the common almost-sure
bound appears only in Bernstein's linear term.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} {m mOmega : MeasurableSpace Omega}
  {mu : Measure Omega} {hm : m ≤ mOmega}

/-- Conditional version of `HasBernsteinMGF`.

The conditional MGF is represented by conditional expectation rather than by
an independent copy.  The inequality is stated `mu`-almost surely for each
admissible Laplace parameter; this is exactly the form needed by the
filtration induction below.-/
structure HasCondBernsteinMGF (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → ℝ) (v b : ℝ≥0) (mu : @Measure Omega mOmega) : Prop where
  aemeasurable : AEMeasurable X mu
  integrable_exp_mul : ∀ t : ℝ, (b : ℝ) * |t| < 1 →
    Integrable (fun omega ↦ exp (t * X omega)) mu
  cond_mgf_le : ∀ t : ℝ, (b : ℝ) * |t| < 1 →
    ∀ᵐ omega ∂mu,
      mu[fun z ↦ exp (t * X z) | m] omega ≤
        exp ((v : ℝ) * t ^ 2 /
          (2 * (1 - (b : ℝ) * |t|)))

namespace HasCondBernsteinMGF

/-- The conditional MGF field, with a name parallel to the unconditional
`HasBernsteinMGF.mgf_le`.-/
theorem ae_condExp_le
    (hX : HasCondBernsteinMGF m hm X v b mu) (t : ℝ)
    (ht : (b : ℝ) * |t| < 1) :
    ∀ᵐ omega ∂mu,
      mu[fun z ↦ exp (t * X z) | m] omega ≤
        exp ((v : ℝ) * t ^ 2 /
          (2 * (1 - (b : ℝ) * |t|))) :=
  hX.cond_mgf_le t ht

end HasCondBernsteinMGF

/-- Conditional bounded-variance Bernstein lemma.

The variance proxy is twice the deterministic upper bound on the conditional
second moment, matching
`hasBernsteinMGF_of_memLp_two_of_ae_abs_le_of_integral_eq_zero`.  The proof
applies that unconditional result on almost every fibre of `condExpKernel`.-/
theorem hasCondBernsteinMGF_of_memLp_two_of_ae_abs_le_of_condExp_ae_eq_zero
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) (X : Omega → ℝ) (hX : MemLp X 2 mu)
    {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hbound : ∀ᵐ omega ∂mu, |X omega| ≤ b)
    (hcenter : mu[X | m] =ᵐ[mu] 0)
    (hsecond : ∀ᵐ omega ∂mu,
      mu[fun z ↦ X z ^ 2 | m] omega ≤ v) :
    HasCondBernsteinMGF m hm X
      ⟨2 * v, mul_nonneg (by norm_num) hv⟩ ⟨b, hb⟩ mu := by
  have hXint : Integrable X mu := hX.integrable (by norm_num)
  have hXsq : Integrable (fun omega ↦ X omega ^ 2) mu :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).1 hX
  refine
    { aemeasurable := hX.aemeasurable
      integrable_exp_mul := ?_
      cond_mgf_le := ?_ }
  · intro t ht
    apply Integrable.of_bound
      ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (exp (|t| * b))
    filter_upwards [hbound] with omega homega
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      t * X omega ≤ |t * X omega| := le_abs_self _
      _ = |t| * |X omega| := abs_mul _ _
      _ ≤ |t| * b := mul_le_mul_of_nonneg_left homega (abs_nonneg _)
  · intro t ht
    have hExpInt : Integrable (fun omega ↦ exp (t * X omega)) mu := by
      apply Integrable.of_bound
        ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
        (exp (|t| * b))
      filter_upwards [hbound] with omega homega
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      apply exp_le_exp.mpr
      calc
        t * X omega ≤ |t * X omega| := le_abs_self _
        _ = |t| * |X omega| := abs_mul _ _
        _ ≤ |t| * b := mul_le_mul_of_nonneg_left homega (abs_nonneg _)
    let Xmk : Omega → ℝ := hX.aestronglyMeasurable.mk X
    have hXeq : X =ᵐ[mu] Xmk := hX.aestronglyMeasurable.ae_eq_mk
    have hXeqKernel : ∀ᵐ omega ∂mu.trim hm,
        X =ᵐ[condExpKernel mu m omega] Xmk := by
      apply Measure.ae_ae_of_ae_comp
      rw [condExpKernel_comp_trim hm]
      exact hXeq
    have hXsqKernel : ∀ᵐ omega ∂mu.trim hm,
        Integrable (fun z ↦ X z ^ 2) (condExpKernel mu m omega) := by
      apply Measure.ae_integrable_of_integrable_comp
      rw [condExpKernel_comp_trim hm]
      exact hXsq
    have hboundKernel : ∀ᵐ omega ∂mu.trim hm,
        ∀ᵐ z ∂condExpKernel mu m omega, |X z| ≤ b := by
      apply Measure.ae_ae_of_ae_comp
      rw [condExpKernel_comp_trim hm]
      exact hbound
    have hmeanKernel : mu[X | m] =ᵐ[mu.trim hm]
        fun omega ↦ ∫ z, X z ∂condExpKernel mu m omega :=
      condExp_ae_eq_trim_integral_condExpKernel hm hXint
    have hsecondKernel : mu[fun z ↦ X z ^ 2 | m] =ᵐ[mu.trim hm]
        fun omega ↦ ∫ z, X z ^ 2 ∂condExpKernel mu m omega :=
      condExp_ae_eq_trim_integral_condExpKernel hm hXsq
    have hcenterTrim : mu[X | m] =ᵐ[mu.trim hm] 0 :=
      stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable
        hm stronglyMeasurable_zero hcenter
    have hsecondTrim :
        mu[fun z ↦ X z ^ 2 | m] ≤ᵐ[mu.trim hm] fun _ ↦ v :=
      StronglyMeasurable.ae_le_trim_of_stronglyMeasurable hm
        stronglyMeasurable_condExp stronglyMeasurable_const hsecond
    have hExpKernel : mu[fun z ↦ exp (t * X z) | m] =ᵐ[mu.trim hm]
        fun omega ↦ ∫ z, exp (t * X z) ∂condExpKernel mu m omega :=
      condExp_ae_eq_trim_integral_condExpKernel hm hExpInt
    apply ae_of_ae_trim hm
    filter_upwards [hXeqKernel, hXsqKernel, hboundKernel,
        hmeanKernel, hsecondKernel, hcenterTrim, hsecondTrim, hExpKernel]
      with omega hXeqOmega hXsqOmega hboundOmega hmeanOmega
        hsecondOmega hcenterOmega hsecondBoundOmega hExpOmega
    have hXmeasOmega : AEStronglyMeasurable X
        (condExpKernel mu m omega) :=
      hX.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable.congr
        hXeqOmega.symm
    have hXlpOmega : MemLp X 2 (condExpKernel mu m omega) :=
      (memLp_two_iff_integrable_sq hXmeasOmega).2 hXsqOmega
    have hmeanZero : ∫ z, X z ∂condExpKernel mu m omega = 0 := by
      rw [← hmeanOmega, hcenterOmega]
      rfl
    have hsecondLe : ∫ z, X z ^ 2 ∂condExpKernel mu m omega ≤ v := by
      rw [← hsecondOmega]
      exact hsecondBoundOmega
    rw [hExpOmega]
    exact (hasBernsteinMGF_of_memLp_two_of_ae_abs_le_of_integral_eq_zero
      X hXlpOmega hv hb hboundOmega hmeanZero hsecondLe).mgf_le t ht

/-- Exponentials of a sum are integrable when both summands have deterministic
almost-sure bounds.  This small lemma supplies the integrability side
condition in the conditional-MGF multiplication rule.-/
theorem integrable_exp_mul_add_of_ae_abs_le
    [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu)
    {BX BY : ℝ} (hBX : ∀ᵐ omega ∂mu, |X omega| ≤ BX)
    (hBY : ∀ᵐ omega ∂mu, |Y omega| ≤ BY) (t : ℝ) :
    Integrable (fun omega ↦ exp (t * (X omega + Y omega))) mu := by
  apply Integrable.of_bound
    (((hX.add hY).const_mul t).exp.aestronglyMeasurable)
    (exp (|t| * (BX + BY)))
  filter_upwards [hBX, hBY] with omega hXomega hYomega
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  calc
    t * (X omega + Y omega) ≤ |t * (X omega + Y omega)| := le_abs_self _
    _ = |t| * |X omega + Y omega| := abs_mul _ _
    _ ≤ |t| * (|X omega| + |Y omega|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |t| * (BX + BY) := by gcongr

/-- A Bernstein MGF bound composes with a conditional Bernstein MGF bound.

The first summand must be measurable with respect to the conditioning
sigma-algebra.  Boundedness is used only to discharge exponential
integrability; the MGF calculation itself keeps the variance proxies additive
and the common scale proxy unchanged.-/
theorem HasBernsteinMGF.add_of_hasCondBernsteinMGF
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} {vX vY b : ℝ≥0}
    (hm : m ≤ mOmega) (hX : HasBernsteinMGF X vX b mu)
    (hXm : StronglyMeasurable[m] X)
    (hY : HasCondBernsteinMGF m hm Y vY b mu)
    {BX BY : ℝ} (hBX : ∀ᵐ omega ∂mu, |X omega| ≤ BX)
    (hBY : ∀ᵐ omega ∂mu, |Y omega| ≤ BY) :
    HasBernsteinMGF (fun omega ↦ X omega + Y omega) (vX + vY) b mu := by
  refine
    { aemeasurable := hX.aemeasurable.add hY.aemeasurable
      integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t _ht
    exact integrable_exp_mul_add_of_ae_abs_le
      hX.aemeasurable hY.aemeasurable hBX hBY t
  · intro t ht
    let C : ℝ := exp ((vY : ℝ) * t ^ 2 /
      (2 * (1 - (b : ℝ) * |t|)))
    let f : Omega → ℝ := fun omega ↦ exp (t * X omega)
    let g : Omega → ℝ := fun omega ↦ exp (t * Y omega)
    have hfMeas : StronglyMeasurable[m] f := by
      simpa only [f, Pi.smul_apply, smul_eq_mul] using
        continuous_exp.comp_stronglyMeasurable (hXm.const_smul t)
    have hgInt : Integrable g mu := hY.integrable_exp_mul t ht
    have hfgInt : Integrable (f * g) mu := by
      have hsum := integrable_exp_mul_add_of_ae_abs_le
        hX.aemeasurable hY.aemeasurable hBX hBY t
      convert hsum using 1
      ext omega
      simp only [f, g, Pi.mul_apply, mul_add, exp_add]
    have hpull : mu[f * g | m] =ᵐ[mu] f * mu[g | m] :=
      condExp_mul_of_stronglyMeasurable_left hfMeas hfgInt hgInt
    have hrightInt : Integrable (f * mu[g | m]) mu :=
      integrable_condExp.congr hpull
    have hCInt : Integrable (fun omega ↦ f omega * C) mu :=
      (hX.integrable_exp_mul t ht).mul_const C
    have hcond := hY.cond_mgf_le t ht
    have hmono : f * mu[g | m] ≤ᵐ[mu] fun omega ↦ f omega * C := by
      filter_upwards [hcond] with omega homega
      exact mul_le_mul_of_nonneg_left homega (exp_nonneg _)
    calc
      mgf (fun omega ↦ X omega + Y omega) mu t =
          ∫ omega, (f * g) omega ∂mu := by
        simp only [mgf, f, g, mul_add, exp_add, Pi.mul_apply]
      _ = ∫ omega, mu[f * g | m] omega ∂mu := by
        rw [integral_condExp hm]
      _ = ∫ omega, f omega * mu[g | m] omega ∂mu :=
        integral_congr_ae hpull
      _ ≤ ∫ omega, f omega * C ∂mu :=
        integral_mono_ae hrightInt hCInt hmono
      _ = mgf X mu t * C := by
        rw [integral_mul_const]
        rfl
      _ ≤ exp ((vX : ℝ) * t ^ 2 /
            (2 * (1 - (b : ℝ) * |t|))) * C := by
        gcongr
        exact hX.mgf_le t ht
      _ = exp (((vX + vY : ℝ≥0) : ℝ) * t ^ 2 /
            (2 * (1 - (b : ℝ) * |t|))) := by
        rw [show C = exp ((vY : ℝ) * t ^ 2 /
          (2 * (1 - (b : ℝ) * |t|))) by rfl, ← exp_add]
        congr 1
        push_cast
        ring

variable (filtration : Filtration ℕ mOmega)

/-- A finite sum of variables bounded by `b` is bounded by `n * b`.
The statement is separated out because it is also useful for proving the
exponential integrability required by martingale MGF arguments.-/
theorem ae_abs_sum_range_le_nat_mul
    {Y : ℕ → Omega → ℝ} {b : ℝ} {n : ℕ}
    (hbound : ∀ i < n, ∀ᵐ omega ∂mu, |Y i omega| ≤ b) :
    ∀ᵐ omega ∂mu,
      |∑ i ∈ range n, Y i omega| ≤ (n : ℝ) * b := by
  have hall : ∀ᵐ omega ∂mu, ∀ i ∈ range n, |Y i omega| ≤ b := by
    rw [(range n).eventually_all]
    intro i hi
    exact hbound i (mem_range.mp hi)
  filter_upwards [hall] with omega homega
  calc
    |∑ i ∈ range n, Y i omega| ≤ ∑ i ∈ range n, |Y i omega| :=
      Finset.abs_sum_le_sum_abs _ (range n)
    _ ≤ ∑ _i ∈ range n, b := by
      gcongr with i hi
      exact homega i hi
    _ = (n : ℝ) * b := by simp

/-- Finite sums of adapted conditional-Bernstein differences satisfy an
ordinary Bernstein MGF bound.  The deterministic variance proxies add and
the common scale proxy is preserved.-/
theorem HasBernsteinMGF.sum_of_hasCondBernsteinMGF
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    {Y : ℕ → Omega → ℝ} {v : ℕ → ℝ≥0} {b : ℝ≥0}
    (hAdapted : StronglyAdapted filtration Y)
    (hzero : HasBernsteinMGF (Y 0) (v 0) b mu)
    (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ omega ∂mu, |Y i omega| ≤ (b : ℝ))
    (hcond : ∀ i < n - 1,
      HasCondBernsteinMGF (filtration i) (filtration.le i)
        (Y (i + 1)) (v (i + 1)) b mu) :
    HasBernsteinMGF (fun omega ↦ ∑ i ∈ range n, Y i omega)
      (∑ i ∈ range n, v i) b mu := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simpa using hzero
      | succ n =>
          have ih' := ih
            (fun i hi ↦ hbound i (by omega))
            (fun i hi ↦ hcond i (by omega))
          have hSmeas : StronglyMeasurable[filtration n]
              (fun omega ↦ ∑ i ∈ range (n + 1), Y i omega) := by
            apply Finset.stronglyMeasurable_fun_sum
            intro i hi
            exact (hAdapted i).mono (filtration.mono (by
              have hi' := mem_range.mp hi
              omega))
          have hSbound : ∀ᵐ omega ∂mu,
              |∑ i ∈ range (n + 1), Y i omega| ≤
                ((n + 1 : ℕ) : ℝ) * (b : ℝ) :=
            ae_abs_sum_range_le_nat_mul
              (fun i hi ↦ hbound i (by omega))
          have hnextBound : ∀ᵐ omega ∂mu,
              |Y (n + 1) omega| ≤ (b : ℝ) :=
            hbound (n + 1) (by omega)
          have hnext : HasCondBernsteinMGF (filtration n)
              (filtration.le n) (Y (n + 1)) (v (n + 1)) b mu :=
            hcond n (by omega)
          simp_rw [sum_range_succ _ (n + 1)]
          exact ih'.add_of_hasCondBernsteinMGF
            (filtration.le n) hSmeas hnext hSbound hnextBound

end ProbabilityTheory
