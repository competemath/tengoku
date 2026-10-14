/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku

-- pointers: MathFin/Actuarial/Insurance.lean
-- main-module: MathFin/Actuarial/ActuarialInsurance.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-insurance-premium-principles
-- source-issue: 85
-- new-defs: expectedValuePremium, variancePremium, stdDevPremium

/-!
Classical loaded premium principles — expected-value `(1 + θ)·μ`, variance
`μ + α·σ²`, standard-deviation `μ + β·σ` — and their nonnegative-loading
bound: each principle prices at or above the pure premium (the mean loss).
The loadings are the safety margins on top of the net premium of
`MathFin/Actuarial/Insurance.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace MathFin

/-- Expected-value premium principle with loading `θ`: `(1 + θ) · μ`. -/
def expectedValuePremium (θ μ : ℝ) : ℝ := (1 + θ) * μ

/-- Variance premium principle with loading `α` on the variance `σ²`:
`μ + α · σ²`. -/
def variancePremium (α μ σ2 : ℝ) : ℝ := μ + α * σ2

/-- Standard-deviation premium principle with loading `β`: `μ + β · σ`. -/
def stdDevPremium (β μ σ : ℝ) : ℝ := μ + β * σ

/-- A nonnegative loading prices at or above the mean: expected-value principle.
@isnad1 id=le.2h2v.s5.c70e65683887 from=translated src=- shape=bb8b1858 vocab=c5af4ee1
-/
theorem expectedValuePremium_ge_mean {θ μ : ℝ} (hθ : 0 ≤ θ) (hμ : 0 ≤ μ) :
    expectedValuePremium θ μ ≥ μ :=
  le_mul_of_one_le_left hμ (le_add_of_nonneg_right hθ)

/-- A nonnegative loading prices at or above the mean: variance principle.
@isnad1 id=le.2h3v.s5.844fe520d907 from=translated src=- shape=b1e86723 vocab=69a51291
-/
theorem variancePremium_ge_mean {α σ2 : ℝ} (μ : ℝ) (hα : 0 ≤ α) (hσ2 : 0 ≤ σ2) :
    variancePremium α μ σ2 ≥ μ :=
  le_add_of_nonneg_right (mul_nonneg hα hσ2)

/-- A nonnegative loading prices at or above the mean: standard-deviation
principle.
@isnad1 id=le.2h3v.s5.15f71c8a612e from=translated src=- shape=b1e86723 vocab=1efeeeab
-/
theorem stdDevPremium_ge_mean {β σ : ℝ} (μ : ℝ) (hβ : 0 ≤ β) (hσ : 0 ≤ σ) :
    stdDevPremium β μ σ ≥ μ :=
  le_add_of_nonneg_right (mul_nonneg hβ hσ)

/-- All three classical premium principles with nonnegative loadings price at
or above the pure premium.
@isnad1 id=and.6h6v.s6.25097fab776c from=translated src=- shape=343be6a8 vocab=73a16b9a
-/
theorem premium_ge_mean (μ σ2 σ θ α β : ℝ) (hμ : 0 ≤ μ) (hσ2 : 0 ≤ σ2)
    (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    expectedValuePremium θ μ ≥ μ ∧ variancePremium α μ σ2 ≥ μ ∧
      stdDevPremium β μ σ ≥ μ :=
  ⟨expectedValuePremium_ge_mean hθ hμ, variancePremium_ge_mean μ hα hσ2,
    stdDevPremium_ge_mean μ hβ hσ⟩

end MathFin
