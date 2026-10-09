module

public import Tengoku.Expdb.Expdb.Basic.PowerAsymptotics
public import Tengoku.Expdb.Expdb.ExponentialSums.LogPhase
public import Tengoku.Expdb.Expdb.ExponentialSums.FixedExponentialSum
public import Tengoku

/-!
# Exponential sum growth exponents

This module formalizes the asymptotic definition of the exponential sum growth exponent from the
blueprint's Exponential sum growth exponents chapter (`beta-chapter`). It defines admissible
model-phase bounds at a fixed scale and defines `β(α)` as the least such exponent.

## Overview

For `α : ℝ≥0`, an exponent `β` is admissible if every model-phase exponential sum at scale
`N = T ^ (α + o(1))` is bounded by `T ^ (β + o(1))`. We show that the admissible exponents
form `[β(α), ∞)` and then specialize the bound to the logarithmic model phase.
-/

@[expose] public section

open Filter Topology
open scoped Expdb FourierTransform NNReal

noncomputable section

namespace Expdb

/-! ## Exponential-sum growth definition -/

/-- The variable exponential sum
`∑ n ∈ [a, b], e(T F(n / N))`. -/
def exponentialSum
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ)
    (T N : VariableObject ℝ) (a b : VariableObject ℕ) :
    VariableObject ℂ :=
  fun i ↦ exponentialSumAt (F i) (T i) (N i) (a i) (b i)

@[simp] theorem exponentialSum_apply
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ)
    (T N : VariableObject ℝ) (a b : VariableObject ℕ) (i : ℕ) :
    exponentialSum F T N a b i = exponentialSumAt (F i) (T i) (N i) (a i) (b i) :=
  rfl

/-- The assertion that `β` is an admissible exponential-sum growth exponent at scale `α`. -/
def IsExponentSumBound (α : ℝ≥0) (β : ℝ) : Prop :=
  ∀ (N T : VariableObject ℝ)
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ)
    (a b : VariableObject ℕ),
    (∀ i, 1 ≤ N i) →
    (∀ i, 1 ≤ T i) →
    T.IsUnbounded →
    IsPowerAsymptotic N T (α : ℝ) →
    IsModelPhaseFunction F →
    (∀ i, N i ≤ (a i : ℝ) ∧ (b i : ℝ) ≤ 2 * N i) →
    IsPowerBounded (exponentialSum F T N a b) T β

/-- The set of admissible exponential-sum growth exponents at scale `α`. -/
def exponentSumBounds (α : ℝ≥0) : Set ℝ :=
  {β : ℝ | IsExponentSumBound α β}

@[simp] theorem mem_exponentSumBounds {α : ℝ≥0} {β : ℝ} :
    β ∈ exponentSumBounds α ↔ IsExponentSumBound α β :=
  Iff.rfl

/-- The exponential sum growth exponent `β(α)` from the blueprint definition `beta-def`. -/
def exponentSumGrowthExponent (α : ℝ≥0) : ℝ :=
  sInf (exponentSumBounds α)

/-! ## Admissible exponents

The candidate set is upward closed, nonempty, and bounded below.

### Monotonicity -/

/-- Admissible exponential-sum bounds are monotone in the exponent. -/
theorem IsExponentSumBound.mono {α : ℝ≥0} {β γ : ℝ}
    (hβ : IsExponentSumBound α β) (hβγ : β ≤ γ) :
    IsExponentSumBound α γ := by
  intro N T F a b hN hT hTunbounded hNT hF hab
  exact (hβ N T F a b hN hT hTunbounded hNT hF hab).mono
    (Filter.Eventually.of_forall hT) hβγ

/-! ### Nonemptiness and lower bound -/

/-! ## The least admissible exponent -/

/-! ## Logarithmic model phase -/

end Expdb
