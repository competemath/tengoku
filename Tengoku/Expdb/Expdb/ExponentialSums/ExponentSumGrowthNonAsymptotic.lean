module

public import Tengoku.Expdb.Expdb.ExponentialSums.ExponentSumGrowth

import Tengoku.Expdb.Expdb.Basic.AutomaticUniformity
public import Tengoku

/-!
# Non-asymptotic exponential sum growth bounds

This module formalizes the non-asymptotic definition of exponential sum exponent from the
blueprint's Exponential sum growth exponents chapter (`beta-chapter`). It gives a fixed-parameter,
epsilon--delta characterization of the exponential sum growth exponent.
-/

@[expose] public section

open Filter Topology
open scoped ContDiff Expdb FourierTransform NNReal

noncomputable section

namespace Expdb

/-! ## Fixed-parameter formulation -/

/-- The fixed data satisfying the hypotheses of the non-asymptotic exponential-sum bound. -/
structure IsModelPhaseSumSetupAt
    (α σ δ : ℝ) (P : ℕ) (C T N : ℝ) (F : ℝ → ℝ) (a b : ℕ) : Prop where
  /-- The phase parameter is above the uniform threshold. -/
  threshold_le_param : C ≤ T
  /-- The scale is at least the lower power allowed by `δ`. -/
  rpow_sub_le_scale : T ^ (α - δ) ≤ N
  /-- The scale is at most the upper power allowed by `δ`. -/
  scale_le_rpow_add : N ≤ T ^ (α + δ)
  /-- The phase approximates the model phase through order `P`. -/
  isApproximateModelPhase : IsApproximateModelPhaseFunction F σ P δ
  /-- The summation interval begins in the dyadic block. -/
  scale_le_start : N ≤ (a : ℝ)
  /-- The summation interval ends in the dyadic block. -/
  end_le_two_mul_scale : (b : ℝ) ≤ 2 * N

/-- The fixed-parameter epsilon--delta bound from the blueprint lemma `beta-asymp`
    (Non-asymptotic definition of `β`). -/
def IsExponentSumBoundNonAsymptotic (α : ℝ≥0) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ σ : ℝ, 0 < σ →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ P : ℕ, 1 ≤ P ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
              IsModelPhaseSumSetupAt (α : ℝ) σ δ P C T N F a b →
              ‖exponentialSumAt F T N a b‖ ≤ C * T ^ (β + ε)

/-! ## From fixed bounds to asymptotic bounds -/

/-! ## Uniform bounds for approximate model phases -/

/-- An approximate model phase with sufficiently small error has a uniform positive first
derivative and uniform bounds on all derivatives through order `P + 1`, with constants depending
only on `σ` and `P`. -/
theorem approximate_model_phase_deriv_bounds
    {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {δ : ℝ} {F : ℝ → ℝ},
        δ ≤ min ((2 : ℝ) ^ (-σ) / 2) 1 →
        IsApproximateModelPhaseFunction F σ P δ →
        HasPhaseFirstDerivLowerBound F ((2 : ℝ) ^ (-σ) / 2) ∧
        HasPhaseDerivBound F (P + 1) K := by
  let B : ℕ → ℝ := fun p ↦ ‖(descPochhammer ℝ p).eval (-σ)‖
  have hBnonneg (p : ℕ) : 0 ≤ B p := norm_nonneg _
  have hB (p : ℕ) (u : phaseInterval) :
      ‖iteratedDerivWithin p (modelPhase σ) phaseInterval u‖ ≤ B p :=
    norm_iteratedDerivWithin_modelPhase_le hσ.le p u.property
  let K : ℝ := 1 + ∑ p ∈ Finset.range (P + 1), B p
  have hK : 1 ≤ K := by
    dsimp [K]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun p _ ↦ hBnonneg p)
  refine ⟨K, hK, ?_⟩
  intro δ F hδ hF
  have hδc : δ ≤ (2 : ℝ) ^ (-σ) / 2 := hδ.trans (min_le_left _ _)
  have hδone : δ ≤ 1 := hδ.trans (min_le_right _ _)
  constructor
  · intro u hu
    have huPos : 0 < (u : ℝ) := zero_lt_one.trans_le hu.1
    have huLower : (2 : ℝ) ^ (-σ) ≤ (u : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos huPos hu.2 (neg_nonpos.mpr hσ.le)
    have he := hF.2 0 (Nat.zero_le P) ⟨u, hu⟩
    rw [Real.norm_eq_abs, abs_le] at he
    simp only [modelPhaseErrorAt, modelPhase, zero_add, iteratedDerivWithin_zero] at he
    linarith
  · intro k hk hkP u hu
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hpP : p ≤ P := by omega
    have hpMem : p ∈ Finset.range (P + 1) := Finset.mem_range.mpr (by omega)
    have he := hF.2 p hpP ⟨u, hu⟩
    rw [modelPhaseErrorAt] at he
    have htriangle :
        ‖iteratedDerivWithin (p + 1) F phaseInterval u‖ ≤
          ‖iteratedDerivWithin (p + 1) F phaseInterval u -
            iteratedDerivWithin p (modelPhase σ) phaseInterval u‖ +
          ‖iteratedDerivWithin p (modelPhase σ) phaseInterval u‖ :=
      norm_le_norm_sub_add _ _
    calc
      ‖iteratedDerivWithin (1 + p) F phaseInterval u‖ ≤ 1 + B p := by
        simpa [Nat.add_comm] using htriangle.trans (add_le_add (he.trans hδone) (hB p ⟨u, hu⟩))
      _ ≤ K := by
        dsimp [K]
        gcongr
        exact Finset.single_le_sum (fun q _ ↦ hBnonneg q) hpMem

/-- The logarithm is an exact approximate model phase at every finite order. -/
theorem isApproximateModelPhaseFunction_log (P : ℕ) :
    IsApproximateModelPhaseFunction Real.log 1 P 0 := by
  refine ⟨isModelPhaseFunction_log.1 0, ?_⟩
  intro p _ u
  rw [modelPhaseErrorAt, iteratedDerivWithin_log_eq_rpow_neg_one, sub_self, norm_zero]

/-! ## Building asymptotic counterexamples -/

/-! ## Equivalence with the asymptotic definition -/

end Expdb
