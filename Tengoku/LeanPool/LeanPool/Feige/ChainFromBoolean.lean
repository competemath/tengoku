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

/--
@isnad1 id=eq.1h5v.s6.1200ed754284 from=translated src=- shape=2eb8ef23 vocab=6553fa9d
-/
@[simp]
theorem booleanChainK_of_lt {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) {j : ℕ} (hj : j < m + 1) :
    booleanChainK γ β σ j =
      twoPointKFinset γ β (chainState σ ⟨j, hj⟩) := by
  simp [booleanChainK, hj]

/--
@isnad1 id=eq.1h5v.s5.5fcd7e0d1a0e from=translated src=- shape=4ec7ca4b vocab=59a970d6
-/
@[simp]
theorem booleanChainK_of_not_lt {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) {j : ℕ} (hj : ¬j < m + 1) :
    booleanChainK γ β σ j = 0 := by
  simp [booleanChainK, hj]

/--
@isnad1 id=eq.0h4v.s5.950c1cd5eeba from=translated src=- shape=c31806db vocab=8759592e
-/
theorem booleanChainK_sentinel {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) :
    booleanChainK γ β σ (m + 1) = 0 := by
  exact booleanChainK_of_not_lt γ β σ (Nat.not_lt.mpr le_rfl)

/--
@isnad1 id=le.0h4v.s4.8c8fb9007a86 from=translated src=- shape=b2ab26f2 vocab=4b8b3b60
-/
theorem twoPointKFinset_nonneg {ι : Type*} [Fintype ι]
    (γ β : ι → ℝ) (S : Finset ι) :
    0 ≤ twoPointKFinset γ β S := by
  exact dirichletK_nonneg _

end Feige
