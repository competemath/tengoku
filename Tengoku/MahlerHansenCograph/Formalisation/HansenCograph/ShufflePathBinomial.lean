/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.GradedFlagProductShuffle
import Tengoku.Seed.Data.Finset.Sort
import Tengoku.Seed.Data.Set.PowersetCard
import Tengoku.Seed.Order.Interval.Finset.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Binomially many shuffle paths

Choosing the `n` left-moving steps among `n + m` positions gives a canonical
shuffle path.  This realizes the binomial coefficient in the graded-product
flag lower bound.
-/

namespace HansenCograph

open Finset

/-- A choice of the `n` positions occupied by left steps in a shuffle of
`n` left and `m` right steps.-/
abbrev Interleaving (n m : ℕ) := Set.powersetCard (Fin (n + m)) n

namespace Interleaving

variable {n m : ℕ}

/-- Left-step positions, embedded into the set of path vertices.-/
def leftSupport (w : Interleaving n m) : Finset (Fin (n + m + 1)) :=
  w.val.map Fin.castSuccEmb

/-- Right-step positions, embedded into the set of path vertices.-/
def rightSupport (w : Interleaving n m) : Finset (Fin (n + m + 1)) :=
  (w.valᶜ : Finset (Fin (n + m))).map Fin.castSuccEmb

@[simp] theorem card_leftSupport (w : Interleaving n m) :
    (leftSupport w).card = n := by
  simp [leftSupport, Set.powersetCard.card_eq]

@[simp] theorem card_rightSupport (w : Interleaving n m) :
    (rightSupport w).card = m := by
  rw [rightSupport, card_map, card_compl, Fintype.card_fin,
    Set.powersetCard.card_eq]
  omega

@[simp] theorem castSucc_mem_leftSupport (w : Interleaving n m)
    (k : Fin (n + m)) : k.castSucc ∈ leftSupport w ↔ k ∈ w.val := by
  simp [leftSupport]

@[simp] theorem castSucc_mem_rightSupport (w : Interleaving n m)
    (k : Fin (n + m)) : k.castSucc ∈ rightSupport w ↔ k ∉ w.val := by
  simp [rightSupport]

/-- The number of left steps strictly before a path vertex.-/
def leftCount (w : Interleaving n m) (k : Fin (n + m + 1)) : ℕ :=
  ((leftSupport w).filter (· < k)).card

/-- The number of right steps strictly before a path vertex.-/
def rightCount (w : Interleaving n m) (k : Fin (n + m + 1)) : ℕ :=
  ((rightSupport w).filter (· < k)).card

theorem leftCount_le (w : Interleaving n m) (k : Fin (n + m + 1)) :
    leftCount w k ≤ n := by
  exact (card_filter_le (leftSupport w) (· < k)).trans_eq
    (card_leftSupport w)

theorem rightCount_le (w : Interleaving n m) (k : Fin (n + m + 1)) :
    rightCount w k ≤ m := by
  exact (card_filter_le (rightSupport w) (· < k)).trans_eq
    (card_rightSupport w)

/-- Left coordinate of the path at a vertex.-/
def left (w : Interleaving n m) (k : Fin (n + m + 1)) : Fin (n + 1) :=
  ⟨leftCount w k, Nat.lt_succ_of_le (leftCount_le w k)⟩

/-- Right coordinate of the path at a vertex.-/
def right (w : Interleaving n m) (k : Fin (n + m + 1)) : Fin (m + 1) :=
  ⟨rightCount w k, Nat.lt_succ_of_le (rightCount_le w k)⟩

theorem filter_lt_succ_eq_insert (S : Finset (Fin (n + m + 1)))
    (k : Fin (n + m)) (hk : k.castSucc ∈ S) :
    S.filter (· < k.succ) = insert k.castSucc (S.filter (· < k.castSucc)) := by
  ext x
  simp only [mem_filter, mem_insert]
  constructor
  · rintro ⟨hxS, hxlt⟩
    by_cases hx : x = k.castSucc
    · exact Or.inl hx
    · exact Or.inr ⟨hxS, by
        apply Fin.mk_lt_mk.mpr
        have hxv := Fin.mk_lt_mk.mp hxlt
        have hne : x.val ≠ k.val := by
          intro heq
          exact hx (Fin.ext heq)
        omega⟩
  · rintro (rfl | ⟨hxS, hxlt⟩)
    · exact ⟨hk, by simp⟩
    · exact ⟨hxS, lt_trans hxlt (by simp)⟩

theorem filter_lt_succ_eq_of_notMem (S : Finset (Fin (n + m + 1)))
    (k : Fin (n + m)) (hk : k.castSucc ∉ S) :
    S.filter (· < k.succ) = S.filter (· < k.castSucc) := by
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hxS, hxlt⟩
    refine ⟨hxS, ?_⟩
    apply Fin.mk_lt_mk.mpr
    have hxv := Fin.mk_lt_mk.mp hxlt
    have hne : x.val ≠ k.val := by
      intro heq
      have hxeq : x = k.castSucc := Fin.ext heq
      rw [hxeq] at hxS
      apply hk
      exact hxS
    omega
  · rintro ⟨hxS, hxlt⟩
    exact ⟨hxS, lt_trans hxlt (by simp)⟩

@[simp] theorem leftCount_zero (w : Interleaving n m) : leftCount w 0 = 0 := by
  simp [leftCount]

@[simp] theorem rightCount_zero (w : Interleaving n m) : rightCount w 0 = 0 := by
  simp [rightCount]

@[simp] theorem leftCount_last (w : Interleaving n m) :
    leftCount w (.last (n + m)) = n := by
  rw [leftCount, filter_eq_self.mpr, card_leftSupport]
  intro x hx
  rcases mem_map.mp hx with ⟨a, _, rfl⟩
  exact Fin.castSucc_lt_last a

@[simp] theorem rightCount_last (w : Interleaving n m) :
    rightCount w (.last (n + m)) = m := by
  rw [rightCount, filter_eq_self.mpr, card_rightSupport]
  intro x hx
  rcases mem_map.mp hx with ⟨a, _, rfl⟩
  exact Fin.castSucc_lt_last a

theorem leftCount_succ_of_mem (w : Interleaving n m) (k : Fin (n + m))
    (hk : k ∈ w.val) :
    leftCount w k.succ = leftCount w k.castSucc + 1 := by
  rw [leftCount, leftCount,
    filter_lt_succ_eq_insert (leftSupport w) k (by simpa)]
  rw [card_insert_of_notMem]
  simp

theorem leftCount_succ_of_notMem (w : Interleaving n m) (k : Fin (n + m))
    (hk : k ∉ w.val) :
    leftCount w k.succ = leftCount w k.castSucc := by
  rw [leftCount, leftCount,
    filter_lt_succ_eq_of_notMem (leftSupport w) k (by simpa)]

theorem rightCount_succ_of_mem (w : Interleaving n m) (k : Fin (n + m))
    (hk : k ∈ w.val) :
    rightCount w k.succ = rightCount w k.castSucc := by
  rw [rightCount, rightCount,
    filter_lt_succ_eq_of_notMem (rightSupport w) k (by simpa)]

theorem rightCount_succ_of_notMem (w : Interleaving n m) (k : Fin (n + m))
    (hk : k ∉ w.val) :
    rightCount w k.succ = rightCount w k.castSucc + 1 := by
  rw [rightCount, rightCount,
    filter_lt_succ_eq_insert (rightSupport w) k (by simpa)]
  rw [card_insert_of_notMem]
  simp

/-- Prefix counts of a finite support attain every value from zero to the
cardinality of that support.-/
theorem exists_card_filter_lt_eq {N r : ℕ} (S : Finset (Fin (N + 1)))
    (hcard : S.card = r) (hlast : ∀ x ∈ S, x < Fin.last N)
    (i : Fin (r + 1)) :
    ∃ k : Fin (N + 1), (S.filter (· < k)).card = i.val := by
  by_cases hi : i = 0
  · subst i
    exact ⟨0, by simp⟩
  · let j : Fin r := i.pred hi
    let e : Fin r ↪o Fin (N + 1) := S.orderEmbOfFin hcard
    have hej_mem : e j ∈ S := by
      exact S.orderEmbOfFin_mem hcard j
    have hej_last : e j < Fin.last N := hlast (e j) hej_mem
    let k : Fin (N + 1) := ⟨(e j).val + 1, by
      change (e j).val < N at hej_last
      omega⟩
    refine ⟨k, ?_⟩
    have hfilter : S.filter (· < k) = S.filter (· ≤ e j) := by
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨hxS, hxk⟩
        refine ⟨hxS, Fin.mk_le_mk.mpr ?_⟩
        have hxk' : x.val < (e j).val + 1 := by
          change x.val < (e j).val + 1 at hxk
          exact hxk
        exact Nat.le_of_lt_succ hxk'
      · rintro ⟨hxS, hxj⟩
        refine ⟨hxS, Fin.mk_lt_mk.mpr ?_⟩
        exact Nat.lt_succ_of_le (Fin.mk_le_mk.mp hxj)
    rw [hfilter]
    have hbij : (Finset.Iic j).card = (S.filter (· ≤ e j)).card := by
      apply Finset.card_bij (fun a _ ↦ e a)
      · intro a ha
        exact mem_filter.mpr ⟨S.orderEmbOfFin_mem hcard a,
          e.monotone (Finset.mem_Iic.mp ha)⟩
      · intro a _ b _ hab
        exact e.injective hab
      · intro x hx
        rcases mem_filter.mp hx with ⟨hxS, hxle⟩
        have hxrange : x ∈ Set.range e := by
          rw [show Set.range e = (S : Set (Fin (N + 1))) by
            exact S.range_orderEmbOfFin hcard]
          exact hxS
        rcases hxrange with ⟨a, rfl⟩
        exact ⟨a, Finset.mem_Iic.mpr (e.le_iff_le.mp hxle), rfl⟩
    rw [← hbij, Fin.card_Iic]
    have hneval : i.val ≠ 0 := by
      intro h
      apply hi
      exact Fin.ext h
    have hival : 0 < i.val := Nat.pos_of_ne_zero hneval
    simp only [j, Fin.val_pred]
    omega

/-- The shuffle path obtained by reading a choice of left-step positions.-/
def toShufflePath (w : Interleaving n m) : ShufflePath n m where
  left := left w
  right := right w
  left_zero := Fin.ext (by simp [left])
  right_zero := Fin.ext (by simp [right])
  left_last := Fin.ext (by simp [left])
  right_last := Fin.ext (by simp [right])
  step k := by
    by_cases hk : k ∈ w.val
    · exact Or.inl ⟨Fin.covBy_iff.mpr (Nat.covBy_iff_add_one_eq.mpr (by
          change leftCount w k.castSucc + 1 = leftCount w k.succ
          exact (leftCount_succ_of_mem w k hk).symm)),
        Fin.ext (by
          change rightCount w k.castSucc = rightCount w k.succ
          exact (rightCount_succ_of_mem w k hk).symm)⟩
    · exact Or.inr ⟨Fin.covBy_iff.mpr (Nat.covBy_iff_add_one_eq.mpr (by
          change rightCount w k.castSucc + 1 = rightCount w k.succ
          exact (rightCount_succ_of_notMem w k hk).symm)),
        Fin.ext (by
          change leftCount w k.castSucc = leftCount w k.succ
          exact (leftCount_succ_of_notMem w k hk).symm)⟩
  left_surjective i := by
    obtain ⟨k, hk⟩ := exists_card_filter_lt_eq (leftSupport w)
      (card_leftSupport w) (by
        intro x hx
        rcases mem_map.mp hx with ⟨a, _, rfl⟩
        exact Fin.castSucc_lt_last a) i
    exact ⟨k, Fin.ext hk⟩
  right_surjective i := by
    obtain ⟨k, hk⟩ := exists_card_filter_lt_eq (rightSupport w)
      (card_rightSupport w) (by
        intro x hx
        rcases mem_map.mp hx with ⟨a, _, rfl⟩
        exact Fin.castSucc_lt_last a) i
    exact ⟨k, Fin.ext hk⟩

theorem mem_iff_left_ne (w : Interleaving n m) (k : Fin (n + m)) :
    k ∈ w.val ↔ left w k.castSucc ≠ left w k.succ := by
  by_cases hk : k ∈ w.val
  · refine ⟨fun _ hEq ↦ ?_, fun _ ↦ hk⟩
    have hv := congrArg Fin.val hEq
    change leftCount w k.castSucc = leftCount w k.succ at hv
    rw [leftCount_succ_of_mem w k hk] at hv
    omega
  · exact ⟨fun h ↦ (hk h).elim, fun hne ↦ (hne (Fin.ext (by
      change leftCount w k.castSucc = leftCount w k.succ
      exact (leftCount_succ_of_notMem w k hk).symm))).elim⟩

theorem toShufflePath_injective : Function.Injective
    (toShufflePath : Interleaving n m → ShufflePath n m) := by
  intro w z hwz
  apply Subtype.ext
  ext k
  rw [mem_iff_left_ne w, mem_iff_left_ne z]
  have hleft := congrArg ShufflePath.left hwz
  change left w = left z at hleft
  rw [hleft]

/-- Interleavings embed into shuffle paths.-/
def embedding (n m : ℕ) : Interleaving n m ↪ ShufflePath n m :=
  ⟨toShufflePath, toShufflePath_injective⟩

end Interleaving

/-- There are at least `choose (n + m) n` shuffle paths.-/
theorem choose_le_card_shufflePath (n m : ℕ) :
    Nat.choose (n + m) n ≤ Nat.card (ShufflePath n m) := by
  have h := Nat.card_le_card_of_injective (Interleaving.embedding n m)
    (Interleaving.embedding n m).injective
  rw [Set.powersetCard.card, Nat.card_fin] at h
  exact h

/-- Binomial graded-product lower bound for maximal-chain sequences.-/
theorem rankedFlag_product_choose_lower_bound
    {P : Type u} {Q : Type v}
    [PartialOrder P] [BoundedOrder P] [Finite P]
    [PartialOrder Q] [BoundedOrder Q] [Finite Q]
    {n m : ℕ} :
    Nat.card (RankedFlag P n) * Nat.card (RankedFlag Q m) *
        Nat.choose (n + m) n ≤
      Nat.card (RankedFlag (P × Q) (n + m)) := by
  calc
    _ ≤ Nat.card (RankedFlag P n) * Nat.card (RankedFlag Q m) *
        Nat.card (ShufflePath n m) :=
      Nat.mul_le_mul_left _ (choose_le_card_shufflePath n m)
    _ ≤ _ := rankedFlag_product_card_lower_bound

end HansenCograph
