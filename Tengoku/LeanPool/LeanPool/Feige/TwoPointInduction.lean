/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.ChainMeasure

/-!
# Finite expectations in the two-point calibration argument

This file defines the independent product expectation and the rejection
payoff used by the ordered insertion proof.
-/

@[expose] public section

open scoped BigOperators

namespace Feige

/-- Expectation under the independent product law on high sets. -/
noncomputable def productHighSetExpectation {m : ℕ}
    (p : Fin m → ℝ) (g : Finset (Fin m) → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset, highSetMass p S * g S

/--
@isnad1 id=eq.0h2v.s4.0d0fbf8405c9 from=translated src=- shape=da2bac75 vocab=1d9c0f83
-/
@[simp]
theorem productHighSetExpectation_one {m : ℕ} (p : Fin m → ℝ) :
    productHighSetExpectation p (fun _ ↦ 1) = 1 := by
  unfold productHighSetExpectation
  simp only [mul_one]
  exact sum_highSetMass p

/--
@isnad1 id=eq.0h4v.s5.2253f343241b from=translated src=- shape=402ac3f8 vocab=454242d2
-/
theorem productExpectation_rejection_eq {m : ℕ}
    (γ β : Fin m → ℝ) (α : ℝ) :
    productHighSetExpectation (twoPointHighProbability γ β)
        (booleanRejectionPayoff γ β α) =
      twoPointRejectionMass γ β α := by
  classical
  unfold productHighSetExpectation booleanRejectionPayoff
    twoPointRejectionMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : twoPointKFinset γ β S ≤ α <;> simp [hS]

end Feige
