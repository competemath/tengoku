/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.InsertionExpectation
public import Tengoku.LeanPool.LeanPool.Feige.Lemma43Insertion

/-!
# Assembly of the analytic insertion edges

This file performs the last finite bookkeeping step in the chain-insertion
argument for Theorem 2.1.  Once each genuine edge of the old chain is
represented by the two signed-exponential endpoint laws from the local
transfer step, and the terminal edge is
represented by its one-sided common law, all positivity, monotonicity, and
transfer hypotheses required by `exists_insertChainPerm_dominates_reveal`
follow automatically.
-/

@[expose] public section

open MeasureTheory

namespace Feige

noncomputable section

/-- The low-side scale of the old coordinate changed at edge `j`; it equals
`1` at the terminal edge, which changes the distinguished exponential. -/
def insertionEdgeScale {n : ℕ}
    (γ : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (j : ℕ) : ℝ :=
  if hj : j < n then γ (σ ⟨j, hj⟩).castSucc else 1

/-- The zero-extended interpolation sequence is identically zero from its
sentinel onward. -/
theorem insertionTheta_eq_zero_of_ge {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    {r : ℕ} (hr : n + 1 ≤ r) :
    insertionTheta γ β σ r = 0 := by
  have hnot : ¬r < n + 1 := Nat.not_lt.mpr hr
  unfold insertionTheta insertionWidth insertionOldK
  rw [booleanChainK_of_not_lt _ _ _ hnot]
  simp [insertionLowerK, insertionUpperK, hnot]

end

end Feige
