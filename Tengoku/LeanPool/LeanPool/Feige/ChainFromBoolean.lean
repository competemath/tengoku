/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.BooleanChain
public import Tengoku.LeanPool.LeanPool.Feige.ChainCalibration
public import Tengoku.LeanPool.LeanPool.Feige.TwoPoint

/-!
# Calibrated statistic sequences along maximal Boolean chains

This file evaluates `twoPointKFinset` on the states of a maximal chain and
extends the resulting finite sequence by zero.  The extension is a
`CalibratedChain`, so the exact telescoping calibration lemma applies
immediately.
-/

@[expose] public section

namespace Feige

/-- The two-point statistic along the maximal chain encoded by `σ`, extended
by zero from the sentinel index `m + 1` onwards. -/
noncomputable def booleanChainK {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (j : ℕ) : ℝ :=
  if hj : j < m + 1 then
    twoPointKFinset γ β (chainState σ ⟨j, hj⟩)
  else
    0

@[simp]
theorem booleanChainK_of_lt {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) {j : ℕ} (hj : j < m + 1) :
    booleanChainK γ β σ j =
      twoPointKFinset γ β (chainState σ ⟨j, hj⟩) := by
  simp [booleanChainK, hj]

@[simp]
theorem booleanChainK_of_not_lt {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) {j : ℕ} (hj : ¬j < m + 1) :
    booleanChainK γ β σ j = 0 := by
  simp [booleanChainK, hj]

theorem booleanChainK_sentinel {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) :
    booleanChainK γ β σ (m + 1) = 0 := by
  exact booleanChainK_of_not_lt γ β σ (Nat.not_lt.mpr le_rfl)

theorem twoPointKFinset_nonneg {ι : Type*} [Fintype ι]
    (γ β : ι → ℝ) (S : Finset ι) :
    0 ≤ twoPointKFinset γ β S := by
  exact dirichletK_nonneg _

end Feige
