/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentConditionalMGF
import Tengoku.Randomsettheory.RandomSetTheory.MartingaleVarianceBernstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# One-sided MGF composition along a filtration

This file provides a generic one-sided counterpart of the Bernstein MGF
composition API.  The exponent is an arbitrary deterministic function
`psi : ℝ → ℝ`, and Laplace parameters are restricted to `t ≥ 0`.  Therefore
only deterministic upper bounds are needed for exponential integrability;
no lower-tail bound is imposed.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} {m mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

/-- An ordinary one-sided MGF certificate with deterministic exponent.-/
structure HasOneSidedMGF (X : Omega → ℝ) (psi : ℝ → ℝ)
    (mu : Measure Omega) : Prop where
  aemeasurable : AEMeasurable X mu
  integrable_exp_mul : ∀ t : ℝ, 0 ≤ t →
    Integrable (fun omega ↦ exp (t * X omega)) mu
  mgf_le : ∀ t : ℝ, 0 ≤ t → mgf X mu t ≤ exp (psi t)

/-- Conditional one-sided MGF certificate.-/
structure HasCondOneSidedMGF (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → ℝ) (psi : ℝ → ℝ)
    (mu : @Measure Omega mOmega) : Prop where
  aemeasurable : AEMeasurable X mu
  integrable_exp_mul : ∀ t : ℝ, 0 ≤ t →
    Integrable (fun omega ↦ exp (t * X omega)) mu
  cond_mgf_le : ∀ t : ℝ, 0 ≤ t →
    ∀ᵐ omega ∂mu,
      mu[fun z ↦ exp (t * X z) | m] omega ≤ exp (psi t)

namespace HasCondOneSidedMGF

theorem ae_condExp_le
    {X : Omega → ℝ} {psi : ℝ → ℝ} {hm : m ≤ mOmega}
    (hX : HasCondOneSidedMGF m hm X psi mu)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ omega ∂mu,
      mu[fun z ↦ exp (t * X z) | m] omega ≤ exp (psi t) :=
  hX.cond_mgf_le t ht

end HasCondOneSidedMGF

/-- Exponentials of a sum are integrable under deterministic upper bounds
when the Laplace parameter is nonnegative.-/
theorem integrable_exp_mul_add_of_ae_le
    [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu)
    {BX BY t : ℝ} (hBX : ∀ᵐ omega ∂mu, X omega ≤ BX)
    (hBY : ∀ᵐ omega ∂mu, Y omega ≤ BY) (ht : 0 ≤ t) :
    Integrable (fun omega ↦ exp (t * (X omega + Y omega))) mu := by
  apply Integrable.of_bound
    (((hX.add hY).const_mul t).exp.aestronglyMeasurable)
    (exp (t * (BX + BY)))
  filter_upwards [hBX, hBY] with omega hXomega hYomega
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (add_le_add hXomega hYomega) ht)

/-- The zero random variable has zero one-sided exponent.-/
@[simp] theorem HasOneSidedMGF.zero [IsProbabilityMeasure mu] :
    HasOneSidedMGF (fun _ : Omega ↦ 0) (fun _ ↦ 0) mu := by
  refine
    { aemeasurable := aemeasurable_const
      integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t _ht
    simpa only [mul_zero, exp_zero] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Omega ↦ (1 : ℝ)) mu)
  · intro t _ht
    simp [mgf]

/-- An ordinary one-sided MGF bound composes with a conditional one.-/
theorem HasOneSidedMGF.add_of_hasCondOneSidedMGF
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} {psiX psiY : ℝ → ℝ}
    (hm : m ≤ mOmega) (hX : HasOneSidedMGF X psiX mu)
    (hXm : StronglyMeasurable[m] X)
    (hY : HasCondOneSidedMGF m hm Y psiY mu)
    {BX BY : ℝ} (hBX : ∀ᵐ omega ∂mu, X omega ≤ BX)
    (hBY : ∀ᵐ omega ∂mu, Y omega ≤ BY) :
    HasOneSidedMGF (fun omega ↦ X omega + Y omega)
      (fun t ↦ psiX t + psiY t) mu := by
  refine
    { aemeasurable := hX.aemeasurable.add hY.aemeasurable
      integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t ht
    exact integrable_exp_mul_add_of_ae_le
      hX.aemeasurable hY.aemeasurable hBX hBY ht
  · intro t ht
    let C : ℝ := exp (psiY t)
    let f : Omega → ℝ := fun omega ↦ exp (t * X omega)
    let g : Omega → ℝ := fun omega ↦ exp (t * Y omega)
    have hfMeas : StronglyMeasurable[m] f := by
      simpa only [f, Pi.smul_apply, smul_eq_mul] using
        continuous_exp.comp_stronglyMeasurable (hXm.const_smul t)
    have hgInt : Integrable g mu := hY.integrable_exp_mul t ht
    have hfgInt : Integrable (f * g) mu := by
      have hsum := integrable_exp_mul_add_of_ae_le
        hX.aemeasurable hY.aemeasurable hBX hBY ht
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
      _ ≤ exp (psiX t) * C := by
        gcongr
        exact hX.mgf_le t ht
      _ = exp (psiX t + psiY t) := by
        rw [show C = exp (psiY t) by rfl, ← exp_add]

/-! ## Finite sums along a filtration -/

variable (filtration : Filtration ℕ mOmega)

/-- A finite sum inherits the sum of deterministic upper bounds.-/
theorem ae_sum_range_le_sum
    {Y : ℕ → Omega → ℝ} {B : ℕ → ℝ} {n : ℕ}
    (hbound : ∀ i < n, ∀ᵐ omega ∂mu, Y i omega ≤ B i) :
    ∀ᵐ omega ∂mu,
      (∑ i ∈ range n, Y i omega) ≤ ∑ i ∈ range n, B i := by
  have hall : ∀ᵐ omega ∂mu, ∀ i ∈ range n, Y i omega ≤ B i := by
    rw [(range n).eventually_all]
    intro i hi
    exact hbound i (mem_range.mp hi)
  filter_upwards [hall] with omega homega
  exact Finset.sum_le_sum fun i hi ↦ homega i hi

/-- Finite sums of strongly adapted conditional one-sided MGF increments
have exponent equal to the sum of their deterministic exponents.-/
theorem HasOneSidedMGF.sum_of_hasCondOneSidedMGF
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    {Y : ℕ → Omega → ℝ} {psi : ℕ → ℝ → ℝ} {B : ℕ → ℝ}
    (hAdapted : StronglyAdapted filtration Y)
    (hzero : HasOneSidedMGF (Y 0) (psi 0) mu)
    (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ omega ∂mu, Y i omega ≤ B i)
    (hcond : ∀ i < n - 1,
      HasCondOneSidedMGF (filtration i) (filtration.le i)
        (Y (i + 1)) (psi (i + 1)) mu) :
    HasOneSidedMGF (fun omega ↦ ∑ i ∈ range n, Y i omega)
      (fun t ↦ ∑ i ∈ range n, psi i t) mu := by
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
              (∑ i ∈ range (n + 1), Y i omega) ≤
                ∑ i ∈ range (n + 1), B i :=
            ae_sum_range_le_sum
              (fun i hi ↦ hbound i (by omega))
          have hnextBound : ∀ᵐ omega ∂mu,
              Y (n + 1) omega ≤ B (n + 1) :=
            hbound (n + 1) (by omega)
          have hnext : HasCondOneSidedMGF (filtration n)
              (filtration.le n) (Y (n + 1)) (psi (n + 1)) mu :=
            hcond n (by omega)
          simp_rw [sum_range_succ _ (n + 1)]
          exact ih'.add_of_hasCondOneSidedMGF
            (filtration.le n) hSmeas hnext hSbound hnextBound

/-! ## Strong-moment constructors -/

/-- The unconditional strong-moment Taylor theorem produces a generic
one-sided MGF certificate.-/
theorem hasOneSidedMGF_of_strongMoment
    [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q) {y : ℝ} (hy : 0 ≤ y)
    (hX : Integrable X mu)
    (hXsq : Integrable (fun omega ↦ X omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega ↦ (max (X omega) 0) ^ k) mu)
    (hupper : ∀ᵐ omega ∂mu, X omega ≤ y)
    (hcenter : (∫ omega, X omega ∂mu) ≤ 0) :
    HasOneSidedMGF X
      (fun t ↦ strongMomentTaylorExponent q t y
        (∫ omega, X omega ^ 2 ∂mu)
        (fun k ↦ ∫ omega, (max (X omega) 0) ^ k ∂mu)) mu := by
  refine
    { aemeasurable := hX.aemeasurable
      integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t ht
    apply Integrable.of_bound
      ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (exp (t * y))
    filter_upwards [hupper] with omega homega
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left homega ht)
  · intro t ht
    exact integral_exp_mul_le_exp_strongMomentTaylorExponent
      X q hq ht hy hX hXsq hpow hupper hcenter

/-- The conditional strong-moment theorem produces a generic conditional
one-sided MGF certificate.-/
theorem hasCondOneSidedMGF_of_strongMoment
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) (X : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {y second : ℝ} (hy : 0 ≤ y)
    (hX : Integrable X mu)
    (hXsq : Integrable (fun omega ↦ X omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega ↦ (max (X omega) 0) ^ k) mu)
    (hupper : ∀ᵐ omega ∂mu, X omega ≤ y)
    (hcenter : mu[X | m] ≤ᵐ[mu] 0)
    (hsecond : mu[fun omega ↦ X omega ^ 2 | m] ≤ᵐ[mu]
      fun _ ↦ second)
    (moment : ℕ → ℝ)
    (hmoment : ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega ↦ (max (X omega) 0) ^ k | m] ≤ᵐ[mu]
        fun _ ↦ moment k) :
    HasCondOneSidedMGF m hm X
      (fun t ↦ strongMomentTaylorExponent q t y second moment) mu := by
  refine
    { aemeasurable := hX.aemeasurable
      integrable_exp_mul := ?_
      cond_mgf_le := ?_ }
  · intro t ht
    apply Integrable.of_bound
      ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (exp (t * y))
    filter_upwards [hupper] with omega homega
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left homega ht)
  · intro t ht
    exact condExp_exp_mul_le_exp_strongMomentTaylorExponent
      hm X q hq ht hy hX hXsq hpow hupper hcenter hsecond moment hmoment

end ProbabilityTheory
