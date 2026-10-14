/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.InsertionAlgebra
public import Tengoku.LeanPool.LeanPool.Feige.ChainInsertion
public import Tengoku.LeanPool.LeanPool.Feige.ChainFromBoolean

/-!
# Statistic values on an inserted Boolean chain

This file connects the concrete inserted Boolean chain to the abstract
`A`/`B` statistic sequences used in the mass-transport proof of Theorem 2.1.
-/

@[expose] public section

namespace Feige

/-- The `Bᵣ` value at the lifted lower state `Cᵣ`, extended by zero after
the old chain's sentinel. -/
noncomputable def insertionLowerK {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  if hr : r < n + 1 then
    twoPointKFinset γ β
      (liftChainState (chainState σ ⟨r, hr⟩))
  else 0

/-- The `Aᵣ` value at the lifted upper state `Hᵣ`, extended by zero after
the old chain's sentinel. -/
noncomputable def insertionUpperK {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  if hr : r < n + 1 then
    twoPointKFinset γ β
      (insert (Fin.last n) (liftChainState (chainState σ ⟨r, hr⟩)))
  else 0

/-- The old `n`-coordinate statistic sequence `Fᵣ`, including its zero
sentinel. -/
noncomputable def insertionOldK {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  booleanChainK (fun i ↦ γ i.castSucc) (fun i ↦ β i.castSucc) σ r

/-- Band width `wᵣ = Bᵣ - Aᵣ`. -/
noncomputable def insertionWidth {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  insertionLowerK γ β σ r - insertionUpperK γ β σ r

/-- Conditional interpolation parameter
`θᵣ = (Fᵣ - Aᵣ) / (Bᵣ - Aᵣ)`. -/
noncomputable def insertionTheta {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  (insertionOldK γ β σ r - insertionUpperK γ β σ r) /
    insertionWidth γ β σ r

/-- The defining interpolation identity, whenever the band has positive
width (nonzero is algebraically sufficient).
@isnad1 id=eq.1h5v.s6.41a9ee11869f from=translated src=- shape=9964fe64 vocab=c7302a9d
-/
theorem insertionOldK_eq_upper_add_theta_mul_width {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ)
    (hw : insertionWidth γ β σ r ≠ 0) :
    insertionOldK γ β σ r =
      insertionUpperK γ β σ r +
        insertionTheta γ β σ r * insertionWidth γ β σ r := by
  unfold insertionTheta
  field_simp [hw]
  ring

/-- The interpolation identity on the whole zero-extended sequence, given
nondegeneracy of every genuine insertion band.
@isnad1 id=eq.1h5v.s6.0fe722516253 from=translated src=- shape=f7efb7b1 vocab=fca17210
-/
theorem insertionOldK_eq_upper_add_theta_mul_width_all {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hw : ∀ r < n + 1, insertionWidth γ β σ r ≠ 0) (r : ℕ) :
    insertionOldK γ β σ r =
      insertionUpperK γ β σ r +
        insertionTheta γ β σ r * insertionWidth γ β σ r := by
  by_cases hr : r < n + 1
  · exact insertionOldK_eq_upper_add_theta_mul_width γ β σ r (hw r hr)
  · have hF : insertionOldK γ β σ r = 0 := by
      exact booleanChainK_of_not_lt _ _ _ hr
    have hA : insertionUpperK γ β σ r = 0 := by
      simp [insertionUpperK, hr]
    have hB : insertionLowerK γ β σ r = 0 := by
      simp [insertionLowerK, hr]
    rw [hF, hA]
    simp [insertionTheta, insertionWidth, hF, hA, hB]

/--
@isnad1 id=eq.0h4v.s6.824b407a3830 from=translated src=- shape=4a1b5736 vocab=7567144e
-/
@[simp]
theorem insertionTheta_sentinel {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) :
    insertionTheta γ β σ (n + 1) = 0 := by
  unfold insertionTheta insertionOldK insertionWidth
    insertionLowerK insertionUpperK
  rw [booleanChainK_sentinel]
  simp

/-- At every genuine level, the statistic along the inserted permutation is
exactly `Bᵣ` before insertion and `Aᵣ₋₁` afterwards.
@isnad1 id=eq.0h6v.s7.6a09ab563091 from=translated src=- shape=2431d43a vocab=d438043d
-/
theorem booleanChainK_insertChainPerm_eq {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (r : Fin (n + 2)) :
    booleanChainK γ β (insertChainPerm σ J) r.val =
      insertionStatisticSequence
        (insertionUpperK γ β σ) (insertionLowerK γ β σ) J.val r.val := by
  rw [booleanChainK_of_lt γ β (insertChainPerm σ J) r.isLt]
  rw [chainState_insertChainPerm_eq_insertedChainState]
  unfold insertionStatisticSequence insertedChainState
  split_ifs with h
  · unfold insertionLowerK
    rw [dite_eq_left (lt_of_le_of_lt h J.isLt)]
  · unfold insertionUpperK
    have hJr : J.val < r.val := Nat.lt_of_not_ge h
    have hrpos : 0 < r.val := lt_of_le_of_lt (Nat.zero_le _) hJr
    have hrlt : r.val - 1 < n + 1 := by omega
    rw [dite_eq_left hrlt]

/-- The preceding identity, including the zero sentinel and the zero
extension beyond it.
@isnad1 id=eq.0h6v.s6.225a3b5a0370 from=translated src=- shape=3d2d2418 vocab=d438043d
-/
theorem booleanChainK_insertChainPerm_eq_nat {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (r : ℕ) :
    booleanChainK γ β (insertChainPerm σ J) r =
      insertionStatisticSequence
        (insertionUpperK γ β σ) (insertionLowerK γ β σ) J.val r := by
  by_cases hr : r < n + 2
  · let rf : Fin (n + 2) := ⟨r, hr⟩
    simpa only [rf] using booleanChainK_insertChainPerm_eq γ β σ J rf
  · rw [booleanChainK_of_not_lt γ β (insertChainPerm σ J) hr]
    unfold insertionStatisticSequence
    rw [ite_eq_right (by omega : ¬r ≤ J.val)]
    unfold insertionUpperK
    rw [dite_eq_right (by omega : ¬r - 1 < n + 1)]

/-- The actual chain mass at a present lower state `Cⱼ` is its lower rank
contribution.
@isnad1 id=eq.1h6v.s7.fc4e8513c4ad from=translated src=- shape=81c96802 vocab=dabab368
-/
theorem chainMass_booleanChainK_insert_lower {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J j : Fin (n + 1)) (hjJ : j ≤ J) :
    chainMass (booleanChainK γ β (insertChainPerm σ J)) j.val =
      lowerMassForInsertion (insertionLowerK γ β σ)
        (fun r ↦ insertionLowerK γ β σ r - insertionUpperK γ β σ r)
        J.val j.val := by
  unfold chainMass
  rw [booleanChainK_insertChainPerm_eq_nat,
    booleanChainK_insertChainPerm_eq_nat]
  simpa only [chainMass] using
    (chainMass_insertionStatisticSequence_lower
      (A := insertionUpperK γ β σ) (B := insertionLowerK γ β σ)
      (w := fun r ↦ insertionLowerK γ β σ r - insertionUpperK γ β σ r)
      hjJ rfl)

/-- The actual chain mass at a present upper state `Hⱼ` is its upper rank
contribution, including the terminal edge to the zero sentinel.
@isnad1 id=eq.1h6v.s7.6d71b84f35f0 from=translated src=- shape=3b2046fa vocab=092092e9
-/
theorem chainMass_booleanChainK_insert_upper {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J j : Fin (n + 1)) (hJj : J ≤ j) :
    chainMass (booleanChainK γ β (insertChainPerm σ J)) (j.val + 1) =
      upperMassForInsertion (insertionUpperK γ β σ) J.val j.val := by
  unfold chainMass
  rw [booleanChainK_insertChainPerm_eq_nat,
    booleanChainK_insertChainPerm_eq_nat]
  simpa only [chainMass] using
    (chainMass_insertionStatisticSequence_upper
      (A := insertionUpperK γ β σ) (B := insertionLowerK γ β σ) hJj)

end Feige
