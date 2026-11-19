/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.ShufflePathBinomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact enumeration of shuffle paths

Every shuffle path is uniquely determined by the positions of its left
steps.  This upgrades the existing embedding of interleavings into shuffle
paths to an equivalence and identifies the exact cardinality.
-/

namespace HansenCograph

theorem ShufflePath.coord_sum_eq {n m : ℕ} (s : ShufflePath n m)
    (i : Fin (n + m + 1)) :
    (s.left i).val + (s.right i).val = i.val := by
  induction i using Fin.induction with
  | zero => simp [s.left_zero, s.right_zero]
  | succ k ih =>
      rcases s.step k with h | h
      · have hl := Nat.covBy_iff_add_one_eq.mp (Fin.covBy_iff.mp h.1)
        have hr := congrArg Fin.val h.2
        change (s.left k.castSucc).val + (s.right k.castSucc).val = k.val at ih
        change (s.left k.castSucc).val + 1 = (s.left k.succ).val at hl
        change (s.right k.castSucc).val = (s.right k.succ).val at hr
        change (s.left k.succ).val + (s.right k.succ).val = k.val + 1
        omega
      · have hr := Nat.covBy_iff_add_one_eq.mp (Fin.covBy_iff.mp h.1)
        have hl := congrArg Fin.val h.2
        change (s.left k.castSucc).val + (s.right k.castSucc).val = k.val at ih
        change (s.right k.castSucc).val + 1 = (s.right k.succ).val at hr
        change (s.left k.castSucc).val = (s.left k.succ).val at hl
        change (s.left k.succ).val + (s.right k.succ).val = k.val + 1
        omega

namespace Interleaving

variable {n m : ℕ}

/-- The positions at which a shuffle path increments its left coordinate.-/
def leftSteps (s : ShufflePath n m) : Finset (Fin (n + m)) :=
  Finset.univ.filter fun k ↦ s.left k.castSucc ≠ s.left k.succ

/-- Left-step positions embedded into the set of path vertices.-/
def leftStepSupport (s : ShufflePath n m) : Finset (Fin (n + m + 1)) :=
  (leftSteps s).map Fin.castSuccEmb

@[simp] theorem castSucc_mem_leftStepSupport (s : ShufflePath n m)
    (k : Fin (n + m)) :
    k.castSucc ∈ leftStepSupport s ↔
      s.left k.castSucc ≠ s.left k.succ := by
  simp [leftStepSupport, leftSteps]

/-- Number of left steps strictly before a path vertex.-/
def leftPrefix (s : ShufflePath n m) (i : Fin (n + m + 1)) : ℕ :=
  ((leftStepSupport s).filter (· < i)).card

@[simp] theorem leftPrefix_zero (s : ShufflePath n m) :
    leftPrefix s 0 = 0 := by
  simp [leftPrefix]

theorem leftPrefix_succ_of_ne (s : ShufflePath n m) (k : Fin (n + m))
    (h : s.left k.castSucc ≠ s.left k.succ) :
    leftPrefix s k.succ = leftPrefix s k.castSucc + 1 := by
  rw [leftPrefix, leftPrefix,
    filter_lt_succ_eq_insert (leftStepSupport s) k (by simpa)]
  rw [Finset.card_insert_of_notMem]
  simp

theorem leftPrefix_succ_of_eq (s : ShufflePath n m) (k : Fin (n + m))
    (h : s.left k.castSucc = s.left k.succ) :
    leftPrefix s k.succ = leftPrefix s k.castSucc := by
  rw [leftPrefix, leftPrefix,
    filter_lt_succ_eq_of_notMem (leftStepSupport s) k (by simpa)]

theorem left_covBy_of_ne (s : ShufflePath n m) (k : Fin (n + m))
    (h : s.left k.castSucc ≠ s.left k.succ) :
    s.left k.castSucc ⋖ s.left k.succ := by
  rcases s.step k with hstep | hstep
  · exact hstep.1
  · exact False.elim (h hstep.2)

/-- The left coordinate is exactly the number of preceding left steps.-/
theorem left_val_eq_leftPrefix (s : ShufflePath n m)
    (i : Fin (n + m + 1)) :
    (s.left i).val = leftPrefix s i := by
  induction i using Fin.induction with
  | zero => simp [leftPrefix, s.left_zero]
  | succ k ih =>
      by_cases h : s.left k.castSucc = s.left k.succ
      · rw [leftPrefix_succ_of_eq s k h]
        have hv := congrArg Fin.val h
        omega
      · rw [leftPrefix_succ_of_ne s k h]
        have hc := Nat.covBy_iff_add_one_eq.mp
          (Fin.covBy_iff.mp (left_covBy_of_ne s k h))
        omega

theorem leftPrefix_last (s : ShufflePath n m) :
    leftPrefix s (.last (n + m)) = (leftStepSupport s).card := by
  rw [leftPrefix, Finset.filter_eq_self.mpr]
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨k, hk, rfl⟩
  exact Fin.castSucc_lt_last k

@[simp] theorem card_leftStepSupport (s : ShufflePath n m) :
    (leftStepSupport s).card = n := by
  calc
    (leftStepSupport s).card = leftPrefix s (.last (n + m)) :=
      (leftPrefix_last s).symm
    _ = (s.left (.last (n + m))).val :=
      (left_val_eq_leftPrefix s (.last (n + m))).symm
    _ = n := by rw [s.left_last]; rfl

@[simp] theorem card_leftSteps (s : ShufflePath n m) :
    (leftSteps s).card = n := by
  simpa [leftStepSupport] using card_leftStepSupport s

/-- Recover the interleaving consisting of the left-step positions.-/
def ofShufflePath (s : ShufflePath n m) : Interleaving n m :=
  Set.powersetCard.ofCard (card_leftSteps s)

theorem toShufflePath_ofShufflePath (s : ShufflePath n m) :
    toShufflePath (ofShufflePath s) = s := by
  apply ShufflePath.ext
  · intro i
    apply Fin.ext
    change leftCount (ofShufflePath s) i = (s.left i).val
    simpa [ofShufflePath, leftPrefix, leftStepSupport, leftSteps,
      leftCount, leftSupport] using (left_val_eq_leftPrefix s i).symm
  · intro i
    have hleft :
        (toShufflePath (ofShufflePath s)).left i = s.left i := by
      apply Fin.ext
      change leftCount (ofShufflePath s) i = (s.left i).val
      simpa [ofShufflePath, leftPrefix, leftStepSupport, leftSteps,
        leftCount, leftSupport] using (left_val_eq_leftPrefix s i).symm
    have hsum₁ := ShufflePath.coord_sum_eq (toShufflePath (ofShufflePath s)) i
    have hsum₂ := ShufflePath.coord_sum_eq s i
    apply Fin.ext
    have hleftval := congrArg Fin.val hleft
    omega

theorem toShufflePath_surjective :
    Function.Surjective
      (toShufflePath : Interleaving n m → ShufflePath n m) :=
  fun s ↦ ⟨ofShufflePath s, toShufflePath_ofShufflePath s⟩

/-- Choices of the left-step positions are equivalent to shuffle paths.-/
noncomputable def equiv (n m : ℕ) :
    Interleaving n m ≃ ShufflePath n m :=
  Equiv.ofBijective toShufflePath
    ⟨toShufflePath_injective, toShufflePath_surjective⟩

/-- The exact binomial enumeration of shuffle paths.-/
theorem card_shufflePath_eq_choose (n m : ℕ) :
    Nat.card (ShufflePath n m) = Nat.choose (n + m) n := by
  calc
    Nat.card (ShufflePath n m) = Nat.card (Interleaving n m) :=
      Nat.card_congr (equiv n m).symm
    _ = Nat.choose (n + m) n := by
      rw [Set.powersetCard.card, Nat.card_fin]

end Interleaving
end HansenCograph
