/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Joachim Breitner
-/
module

public import Tengoku

/-!
# Minimal and maximal layers of a set

This file defines `Set.minLayer` and `Set.maxLayer` as the sets obtained from iterated application
of `Minimal`/`Maximal` on a set, excluding earlier layers.

## Main declarations

* `Set.minLayer` (`Set.maxLayer`): the `n`th minimal (maximal) layer of the given set `A`.
* `Set.pairwiseDisjoint_minLayer` (`Set.pairwiseDisjoint_maxLayer`),
  `Set.isAntichain_minLayer` (`Set.isAntichain_maxLayer`):
  minimal (maximal) layers are pairwise disjoint antichains.
* `Set.iUnion_minLayer_iff_bounded_series`: if the length of `LTSeries` in `A` is bounded,
  `A` equals the union of its `minLayer`s up to `n`.
-/

@[expose] public section

-- Upstreaming status: the file generally looks useful and should go into mathlib;
-- the code can probably be polished and golfed more

namespace Set

variable {α : Type*} [PartialOrder α]

/-- The `n`th minimal layer of `A`. -/
def minLayer (A : Set α) (n : ℕ) : Set α :=
  {a | Minimal (· ∈ A \ ⋃ (k < n), A.minLayer k) a}

/-- The `n`th maximal layer of `A`. -/
def maxLayer (A : Set α) (n : ℕ) : Set α :=
  A.minLayer (α := αᵒᵈ) n

/-- The elements above `A`'s `n` minimal layers. -/
def layersAbove (A : Set α) (n : ℕ) : Set α :=
  A \ ⋃ (k ≤ n), A.minLayer k

/-- The elements below `A`'s `n` maximal layers. -/
def layersBelow (A : Set α) (n : ℕ) : Set α :=
  A \ ⋃ (k ≤ n), A.maxLayer k

variable {A : Set α} {m n : ℕ} {a : α}

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h3v.s6.066e1bc4b83f from=translated src=- shape=e93a013d vocab=3c8b3d00
-/
lemma maxLayer_def : A.maxLayer n = {a | Maximal (· ∈ A \ ⋃ (k < n), A.maxLayer k) a} := by
  rw [maxLayer, minLayer]; rfl

/--
@isnad1 id=le.0h3v.s4.2418842c0e6b from=translated src=- shape=2f734e37 vocab=cf4da912
-/
lemma minLayer_subset : A.minLayer n ⊆ A :=
  calc
    _ ⊆ A \ ⋃ (k < n), A.minLayer k := by
      rw [minLayer]; refine fun _ h ↦ ?_; rw [mem_ofPred] at h; exact h.prop
    _ ⊆ A := sdiff_subset

/--
@isnad1 id=le.0h3v.s4.24bf293660bd from=translated src=- shape=2f734e37 vocab=98966279
-/
lemma maxLayer_subset : A.maxLayer n ⊆ A := minLayer_subset

/--
@isnad1 id=le.0h3v.s4.b44821bce173 from=translated src=- shape=2f734e37 vocab=5e10cbb7
-/
lemma layersAbove_subset : A.layersAbove n ⊆ A := sdiff_subset

/--
@isnad1 id=le.0h3v.s4.36bfa3716148 from=translated src=- shape=2f734e37 vocab=97ff9416
-/
lemma layersBelow_subset : A.layersBelow n ⊆ A := sdiff_subset

-- XXX(MR): should this and `maxLayer_zero` be simp?
/--
@isnad1 id=eq.0h2v.s5.cd3cbd3f6f5d from=translated src=- shape=c4c4c874 vocab=5d510b8e
-/
lemma minLayer_zero : A.minLayer 0 = {a | Minimal (· ∈ A) a} := by rw [minLayer]; simp

/--
@isnad1 id=eq.0h2v.s5.1d4df1c297ba from=translated src=- shape=c4c4c874 vocab=302c121a
-/
lemma maxLayer_zero : A.maxLayer 0 = {a | Maximal (· ∈ A) a} := by rw [maxLayer_def]; simp

/--
@isnad1 id=disjoint.1h4v.s5.4a51cb299ab5 from=translated src=- shape=85af247f vocab=1cfe1866
-/
lemma disjoint_minLayer_of_ne (h : m ≠ n) : Disjoint (A.minLayer m) (A.minLayer n) := by
  wlog hl : m < n generalizing m n; · exact (this h.symm (by lia)).symm
  rw [disjoint_right]; intro p hp
  rw [minLayer] at hp; replace hp := hp.1.2; contrapose! hp
  exact mem_iUnion₂_of_mem hl hp

/--
@isnad1 id=disjoint.1h4v.s5.bbf1b3c88328 from=translated src=- shape=85af247f vocab=31cd8f60
-/
lemma disjoint_maxLayer_of_ne (h : m ≠ n) : Disjoint (A.maxLayer m) (A.maxLayer n) :=
  disjoint_minLayer_of_ne h

/--
@isnad1 id=pairwise.0h2v.s5.fa0c52c77730 from=translated src=- shape=915be36c vocab=3ded2d1b
-/
lemma pairwiseDisjoint_minLayer : univ.PairwiseDisjoint A.minLayer := fun _ _ _ _ ↦
  disjoint_minLayer_of_ne

/--
@isnad1 id=pairwise.0h2v.s5.53beaf9bd522 from=translated src=- shape=915be36c vocab=abb3f113
-/
lemma pairwiseDisjoint_maxLayer : univ.PairwiseDisjoint A.maxLayer := fun _ _ _ _ ↦
  disjoint_minLayer_of_ne

/--
@isnad1 id=isantich.0h3v.s4.4eaa07e404fd from=translated src=- shape=2d215e2d vocab=741e6555
-/
lemma isAntichain_minLayer : IsAntichain (· ≤ ·) (A.minLayer n) := by
  rw [minLayer]; apply setOfPred_minimal_antichain

/--
@isnad1 id=isantich.0h3v.s4.a32c4b343997 from=translated src=- shape=2d215e2d vocab=fbd23cb3
-/
lemma isAntichain_maxLayer : IsAntichain (· ≤ ·) (A.maxLayer n) := by
  rw [maxLayer_def]; apply setOfPred_maximal_antichain

/--
@isnad1 id=ex.2h5v.s5.b8f8df9e7c1d from=translated src=- shape=0d9a8b33 vocab=8238ada9
-/
lemma exists_le_in_minLayer_of_le (ha : a ∈ A.minLayer n) (hm : m ≤ n) :
    ∃ c ∈ A.minLayer m, c ≤ a := by
  induction n, hm using Nat.le_induction generalizing a with
  | base => use a
  | succ n _ ih =>
    have nma : a ∉ A.minLayer n :=
      disjoint_right.mp (disjoint_minLayer_of_ne (by lia)) ha
    rw [minLayer, mem_ofPred, minimal_iff] at ha nma
    have al : a ∈ A \ ⋃ (l < n), A.minLayer l := by
      have : a ∈ A \ ⋃ (k < n + 1), A.minLayer k := ha.1
      push (_ ∈ _) at this ⊢; push Not at this ⊢
      exact ⟨this.1, fun l hl h ↦ this.2 l (Nat.lt_succ_of_lt hl) h⟩
    simp_rw [al, true_and] at nma; push Not at nma; obtain ⟨a', ha', la⟩ := nma
    have ma' : a' ∈ A.minLayer n := by
      by_contra h
      have a'l : a' ∈ A \ ⋃ (l < n + 1), A.minLayer l := by
        have : ∀ l, l < n + 1 ↔ l < n ∨ l = n := by lia
        simp_all [iUnion_or, iUnion_union_distrib]
      exact absurd (ha.2 a'l la.1) (ne_eq _ _ ▸ la.2)
    obtain ⟨c, mc, lc⟩ := ih ma'; use c, mc, lc.trans la.1

/--
@isnad1 id=ex.2h5v.s5.2ed1caf62b12 from=translated src=- shape=35f24d47 vocab=bc54de19
-/
lemma exists_le_in_maxLayer_of_le (ha : a ∈ A.maxLayer n) (hm : m ≤ n) :
    ∃ c ∈ A.maxLayer m, a ≤ c := exists_le_in_minLayer_of_le (α := αᵒᵈ) ha hm

open Order

-- XXX: is this in mathlib already/can it also be removed?
/--
@isnad1 id=iff.1h4v.s7.0e411d3b0400 from=translated src=- shape=b5f5e54f vocab=c635a681
-/
lemma subtype_mk_minimal_iff (α : Type*) [Preorder α]
    (s : Set α) (t : Set s) (x : α) (hx : x ∈ s) :
    Minimal (· ∈ t) (⟨x, hx⟩ : s) ↔ Minimal (fun y ↦ ∃ h, y ∈ s ∧ ⟨y, h⟩ ∈ t) x := by
  wlog hxt : (⟨x, hx⟩ : s) ∈ t
  · have : ¬Minimal (· ∈ t) (⟨x, hx⟩ : s) := by contrapose! hxt; exact hxt.prop
    simp_rw [this, false_iff, exists_and_left]; clear this; contrapose! hxt
    have : x ∈ {y | y ∈ s ∧ ∃ (x : y ∈ s), ⟨y, x⟩ ∈ t} := hxt.prop
    simp_all
  simp +contextual [← OrderEmbedding.minimal_mem_image_iff
    (f := ⟨Function.Embedding.subtype (· ∈ s), by simp⟩) hxt]

/-- `A.minLayer n` comprises exactly `A`'s elements of height `n`.
@isnad1 id=eq.0h3v.s6.076c60cbbb97 from=translated src=- shape=986250f7 vocab=08656d96
-/
lemma minLayer_eq_setOf_height : A.minLayer n = {x | ∃ hx : x ∈ A, height (⟨x, hx⟩ : A) = n} := by
  induction n using Nat.strongRec with
  | ind n ih =>
    ext x
    simp only [mem_ofPred_eq]
    wlog hxs : x ∈ A
    · simp only [hxs, IsEmpty.exists_iff, iff_false]
      contrapose! hxs; exact minLayer_subset hxs
    simp only [hxs, exists_true_left]
    rw [minLayer]
    simp_rw [height_eq_coe_iff_minimal_le_height]
    simp +contextual only [ih]; clear ih
    have : Minimal (n ≤ height ·) (⟨x, hxs⟩ : A) ↔
        Minimal (· ∈ {y | n ≤ height y}) (⟨x, hxs⟩ : A) := Eq.to_iff rfl
    rw [this, subtype_mk_minimal_iff, mem_ofPred]
    congr! 2 with y
    wlog hys : y ∈ A
    · simp [hys]
    simp only [mem_sdiff, hys, mem_iUnion, exists_prop, not_exists, not_and, true_and, mem_ofPred_eq,
      exists_true_left]
    cases height (⟨y, hys⟩ : A)
    · simp
    · simp only [Nat.cast_inj, Nat.cast_le]
      exact ⟨fun h ↦ by contrapose! h; simp [h], fun h m hm ↦ by lia⟩

/--
@isnad1 id=iff.0h3v.s7.4a36fae840b1 from=translated src=- shape=214b37dc vocab=645e18c0
-/
lemma iUnion_lt_minLayer_iff_bounded_series :
    ⋃ (k < n), A.minLayer k = A ↔ ∀ p : LTSeries A, p.length < n := by
  refine ⟨fun h p ↦ ?_, fun hlength ↦ ?_⟩
  · have hx : p.last.1 ∈ ⋃ (k < n), A.minLayer k := h.symm ▸ p.last.2
    simp only [minLayer_eq_setOf_height] at hx
    push _ ∈ _ at hx
    simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const] at hx
    obtain ⟨i, hix, hi⟩ := hx
    have hh := length_le_height_last (p := p)
    rw [hi, Nat.cast_le] at hh
    exact hh.trans_lt hix
  · ext x
    simp only [minLayer_eq_setOf_height]; push _ ∈ _
    wlog hxs : x ∈ A; · simp [hxs]
    simp only [hxs, exists_true_left, iff_true]
    suffices height (⟨x, hxs⟩ : A) < n by
      revert this
      cases height (⟨x, hxs⟩ : A) <;> simp
    cases n with
    | zero =>
      specialize hlength (RelSeries.singleton _ ⟨x, hxs⟩)
      simp at hlength
    | succ n =>
      simp only [Nat.lt_succ_iff] at hlength
      apply lt_of_le_of_lt (b := ↑n) _ (mod_cast lt_add_one n)
      exact iSup_le fun _ ↦ by simp [hlength]

/-- `A` equals the union of its `minLayer`s up to `n` iff
all `LTSeries` in `A` have length at most `n`.
@isnad1 id=iff.0h3v.s7.eb3e845fe101 from=translated src=- shape=ef007434 vocab=5680c4f5
-/
lemma iUnion_minLayer_iff_bounded_series :
    ⋃ (k ≤ n), A.minLayer k = A ↔ ∀ p : LTSeries A, p.length ≤ n := by
  simp_rw [← Nat.lt_succ_iff, iUnion_lt_minLayer_iff_bounded_series]

/--
@isnad1 id=ex.2h5v.s5.380702f39bf5 from=translated src=- shape=b8233513 vocab=83ebdf57
-/
lemma exists_le_in_layersAbove_of_le [Finite α] (ha : a ∈ A.layersAbove n) (hm : m ≤ n) :
    ∃ c ∈ A.minLayer m, c ≤ a := by
  classical
  have ma : a ∈ A \ ⋃ (l' < n), A.minLayer l' := by
    simp only [layersAbove] at ha ⊢
    push _ ∈ _ at ha ⊢; push Not at ha ⊢
    exact ⟨ha.1, fun l' hl' h ↦ ha.2 l' hl'.le h⟩
  have := Fintype.ofFinite α
  let C : Finset α :=
    (A.toFinset \ (Finset.range n).biUnion fun l ↦ (A.minLayer l).toFinset).filter (· ≤ a)
  have Cn : C.Nonempty := by use a; simp_all [C]
  obtain ⟨a', ma', mina'⟩ := C.exists_minimal Cn
  simp_rw [C, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, not_exists,
    not_and, mem_toFinset] at ma' mina'
  conv at mina' => enter [x]; rw [and_imp]
  have ma'₁ : a' ∈ A.minLayer n := by
    rw [minLayer, mem_ofPred, minimal_iff]
    push _ ∈ _; push Not
    exact ⟨ma'.1, fun y hy ly ↦ le_antisymm (mina' hy (ly.trans ma'.2) ly) ly⟩
  obtain ⟨c, mc, lc⟩ := exists_le_in_minLayer_of_le ma'₁ hm
  use c, mc, lc.trans ma'.2

/--
@isnad1 id=ex.2h5v.s5.52815df9688d from=translated src=- shape=71ef1fa7 vocab=cb4ad233
-/
lemma exists_le_in_layersBelow_of_le [Finite α] (ha : a ∈ A.layersBelow n) (hm : m ≤ n) :
    ∃ c ∈ A.maxLayer m, a ≤ c := exists_le_in_layersAbove_of_le (α := αᵒᵈ) ha hm

end Set
