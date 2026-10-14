/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.InsertionK
public import Tengoku.LeanPool.LeanPool.Feige.ChainMeasure

/-!
# Expectations on inserted maximal chains

This file rewrites the chain expectation in terms of the direct inserted
states.  Together with `InsertionK` and `InsertionAlgebra`, it is the bridge
from concrete Boolean chains to the pairwise mass-transport calculation in
the proof of Theorem 2.1.
-/

@[expose] public section

open scoped BigOperators

namespace Feige

/-- Payoff at a lifted lower state `Cᵣ`, with a harmless zero extension. -/
noncomputable def insertionLowerPayoff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (g : Finset (Fin (n + 1)) → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r < n + 1 then
    g (liftChainState (chainState σ ⟨r, hr⟩))
  else 0

/-- Payoff at a lifted upper state `Hᵣ`, with a harmless zero extension. -/
noncomputable def insertionUpperPayoff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (g : Finset (Fin (n + 1)) → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r < n + 1 then
    g (insert (Fin.last n) (liftChainState (chainState σ ⟨r, hr⟩)))
  else 0

/-- Payoff after independently revealing the new last coordinate with
probability `p`. -/
noncomputable def revealedLastPayoff {n : ℕ}
    (p : ℝ) (g : Finset (Fin (n + 1)) → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (1 - p) * g (liftChainState S) +
    p * g (insert (Fin.last n) (liftChainState S))

/-- An increasing Boolean-lattice payoff is increasing on every insertion
pair `Cᵣ ⊆ Hᵣ`.
@isnad1 id=le.1h4v.s6.d7e5b5dae17a from=translated src=- shape=f8ed0f6d vocab=103dfad9
-/
theorem insertionLowerPayoff_le_upperPayoff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) {g : Finset (Fin (n + 1)) → ℝ}
    (hg : Monotone g) (r : ℕ) :
    insertionLowerPayoff σ g r ≤ insertionUpperPayoff σ g r := by
  by_cases hr : r < n + 1
  · rw [insertionLowerPayoff, dite_eq_left hr,
      insertionUpperPayoff, dite_eq_left hr]
    exact hg (Finset.subset_insert _ _)
  · simp [insertionLowerPayoff, insertionUpperPayoff, hr]

/-- Each level term in the abstract insertion score is the corresponding
term of the concrete inserted Boolean-chain expectation.
@isnad1 id=eq.0h7v.s7.a8ee7890dcdb from=translated src=- shape=c9570454 vocab=b61a1b3a
-/
theorem insertionLevelScore_eq_booleanChainTerm {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (g : Finset (Fin (n + 1)) → ℝ)
    (r : Fin (n + 2)) :
    insertionLevelScore
        (insertionUpperK γ β σ) (insertionLowerK γ β σ)
        (fun q ↦ insertionLowerK γ β σ q - insertionUpperK γ β σ q)
        (insertionLowerPayoff σ g) (insertionUpperPayoff σ g)
        J.val r.val =
      chainMass (booleanChainK γ β (insertChainPerm σ J)) r.val *
        g (insertedChainState σ J r) := by
  by_cases h : r.val ≤ J.val
  · let j : Fin (n + 1) := ⟨r.val, lt_of_le_of_lt h J.isLt⟩
    have hjJ : j ≤ J := h
    unfold insertionLevelScore insertionLowerPayoff
    rw [ite_eq_left h, dite_eq_left j.isLt]
    rw [← chainMass_booleanChainK_insert_lower γ β σ J j hjJ]
    unfold insertedChainState
    rw [dite_eq_left h]
  · have hJr : J.val < r.val := Nat.lt_of_not_ge h
    have hrpos : 0 < r.val := lt_of_le_of_lt (Nat.zero_le _) hJr
    let j : Fin (n + 1) := ⟨r.val - 1, by omega⟩
    have hJj : J ≤ j := by
      change J.val ≤ j.val
      simp only [j]
      omega
    unfold insertionLevelScore insertionUpperPayoff
    rw [ite_eq_right h, dite_eq_left j.isLt]
    rw [← chainMass_booleanChainK_insert_upper γ β σ J j hJj]
    unfold insertedChainState
    rw [dite_eq_right h]
    congr 3
    all_goals simp only [j]
    all_goals omega

end Feige
