/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.ChainFromBoolean

/-!
# Probability measures carried by maximal chains

The auxiliary chain distribution mentioned in the proof outline is a finite
probability mass function on the levels of a maximal chain.  This file
packages its expectation and relates the indicator of a threshold rejection
event to `rejectedMass`.
-/

@[expose] public section

open scoped BigOperators

namespace Feige

namespace CalibratedChain

variable {m : ℕ} (C : CalibratedChain m)

/-- Expectation of a payoff on the `m + 1` genuine levels of a calibrated
chain. -/
noncomputable def expectation (g : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), chainMass C.K j * g j

/--
@isnad1 id=eq.0h2v.s4.339533944fce from=translated src=- shape=3e46e687 vocab=362b1bf1
-/
theorem expectation_one : C.expectation (fun _ ↦ 1) = 1 := by
  simp only [expectation, mul_one]
  exact C.total_mass

/--
@isnad1 id=le.1h3v.s5.a17927aaee7b from=translated src=- shape=785014e5 vocab=8169ef46
-/
theorem expectation_nonneg {g : ℕ → ℝ} (hg : ∀ j < m + 1, 0 ≤ g j) :
    0 ≤ C.expectation g := by
  unfold expectation
  exact Finset.sum_nonneg fun j hj ↦
    mul_nonneg (C.mass_nonneg j) (hg j (Finset.mem_range.mp hj))

/-- The rejection indicator used for exact chain calibration. -/
noncomputable def rejectionIndicator (α : ℝ) (j : ℕ) : ℝ :=
  if C.K j ≤ α then 1 else 0

/-- Expectation of the rejection indicator is exactly the previously
defined rejection mass.
@isnad1 id=eq.0h3v.s4.131d71a1b1d0 from=translated src=- shape=ddbcc9ba vocab=63bb6b29
-/
theorem expectation_rejectionIndicator (α : ℝ) :
    C.expectation (C.rejectionIndicator α) = C.rejectedMass α := by
  classical
  simp only [expectation, rejectionIndicator, rejectedMass]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : C.K j ≤ α <;> simp [hj]

/-- Exact calibration in expectation form.
@isnad1 id=le.1h3v.s4.4fd378dd76b0 from=translated src=- shape=d820540c vocab=e87693e1
-/
theorem expectation_rejection_le {α : ℝ} (hα : 0 ≤ α) :
    C.expectation (C.rejectionIndicator α) ≤ α := by
  rw [C.expectation_rejectionIndicator]
  exact C.exact_chain_calibration' hα

end CalibratedChain

section BooleanChain

/-- Increasing rejection payoff on the Boolean lattice. -/
noncomputable def booleanRejectionPayoff {m : ℕ}
    (γ β : Fin m → ℝ) (α : ℝ) (S : Finset (Fin m)) : ℝ :=
  if twoPointKFinset γ β S ≤ α then 1 else 0

end BooleanChain

end Feige
