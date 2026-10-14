/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# Finite-chain functions

A "finite-chain" function is an injective function
  `f : α → α` such that `α ∖ f(α)` is finite.
We prove some properties of finite-chain functions.
-/

@[expose] public section

namespace IMOSL
namespace IMO2013A5

open Function Finset

structure FinChainFn (f : α → α) where
  injective' : f.Injective
  rangeCompl' : Finset α
  rangeCompl_spec' : (rangeCompl' : Set α) = (Set.range f)ᶜ

namespace FinChainFn

section General

variable {f : α → α} (h : FinChainFn f)
include h

/--
@isnad1 id=injectiv.0h3v.s3.dbe610974fd6 from=translated src=- shape=47f51d77 vocab=de46d5f7
-/
theorem injective : f.Injective := h.injective'

def rangeCompl : Finset α := h.rangeCompl'

/--
@isnad1 id=eq.0h3v.s5.6dc7723d36ce from=translated src=- shape=5de41482 vocab=62b03f50
-/
theorem rangeCompl_spec : (h.rangeCompl : Set α) = (Set.range f)ᶜ :=
  h.rangeCompl_spec'

/--
@isnad1 id=iff.0h4v.s5.ba8f5b3310dd from=translated src=- shape=97f566bd vocab=f8290b50
-/
theorem mem_rangeCompl_iff : a ∈ h.rangeCompl ↔ a ∉ Set.range f :=
  Set.ext_iff.mp h.rangeCompl_spec a

/--
@isnad1 id=iff.0h3v.s4.bfb66d1c47e8 from=translated src=- shape=f9e91e9a vocab=cbd3f23d
-/
theorem surjective_iff : f.Surjective ↔ h.rangeCompl = ∅ := by
  rw [← Set.range_eq_univ, ← compl_inj_iff,
    ← h.rangeCompl_spec, Set.compl_univ, coe_eq_empty]

/--
@isnad1 id=ne.3h7v.s6.b4e66dc7582f from=translated src=- shape=6291e532 vocab=bf1eca14
-/
theorem iter_apply_ne_of_mem_rangeCompl_iter_ne (h0 : m ≠ n)
    (h1 : a ∈ h.rangeCompl) (h2 : b ∈ h.rangeCompl) : f^[m] a ≠ f^[n] b := by
  wlog h3 : m < n
  · exact (this h h0.symm h2 h1 <| (le_of_not_gt h3).lt_of_ne h0.symm).symm
  -- Solve assuming `m < n`
  rcases Nat.exists_eq_add_of_le h3.le with ⟨k, rfl⟩
  rw [Nat.lt_add_right_iff_pos] at h3
  rw [f.iterate_add_apply m k b, (h.injective.iterate m).ne_iff]
  rintro rfl; rw [mem_rangeCompl_iff, Set.mem_range] at h1
  refine h1 ⟨f^[k.pred] b, ?_⟩
  rw [← f.iterate_succ_apply', Nat.succ_pred_eq_of_pos h3]

/--
@isnad1 id=and.3h7v.s6.119549dd1352 from=translated src=- shape=6d4a4f7b vocab=bf1eca14
-/
theorem iter_injective (h0 : a ∈ h.rangeCompl) (h1 : b ∈ h.rangeCompl)
    (h2 : f^[m] a = f^[n] b) : m = n ∧ a = b :=
  (eq_or_ne m n).elim
    (λ h3 ↦ ⟨h3, h.injective.iterate n <| by rw [← h2, h3]⟩)
    (λ h3 ↦ absurd h2 (h.iter_apply_ne_of_mem_rangeCompl_iter_ne h3 h0 h1))

/--
@isnad1 id=iff.2h7v.s6.07ce7364638f from=translated src=- shape=af3b9617 vocab=bf1eca14
-/
theorem iter_eq_iff (h0 : a ∈ h.rangeCompl) (h1 : b ∈ h.rangeCompl) :
    f^[m] a = f^[n] b ↔ m = n ∧ a = b :=
  ⟨h.iter_injective h0 h1, λ h2 ↦ congr_arg₂ _ h2.1 h2.2⟩

end General

section Decidable

variable [DecidableEq α] {f : α → α} (h : FinChainFn f)

def exactIterRange (n : ℕ) : Finset α := h.rangeCompl.image f^[n]

/--
@isnad1 id=eq.0h4v.s5.ff5d8accb38a from=translated src=- shape=15129918 vocab=75cf0ce8
-/
theorem exactIterRange_def (n : ℕ) : h.exactIterRange n = h.rangeCompl.image f^[n] := rfl

/--
@isnad1 id=iff.0h5v.s5.085a241356c2 from=translated src=- shape=af2e0acc vocab=2f1f4e38
-/
theorem mem_exactIterRange_iff : a ∈ h.exactIterRange n ↔ ∃ b ∈ h.rangeCompl, f^[n] b = a :=
  mem_image

/--
@isnad1 id=eq.0h4v.s5.02198926aee6 from=translated src=- shape=11ad8be3 vocab=0997aee6
-/
theorem exactIterRange_spec (n : ℕ) :
    (h.exactIterRange n : Set α) = Set.range f^[n] \ Set.range f^[n + 1] :=
  Set.ext λ a ↦ by
    rw [exactIterRange, coe_image, h.rangeCompl_spec, iterate_succ,
      Set.range_comp _ f, Set.range_sdiff_image (h.injective.iterate n)]

/--
@isnad1 id=eq.0h3v.s4.4b385d3537a9 from=translated src=- shape=79d65f8f vocab=cd7c0ebe
-/
theorem exactIterRange_zero : h.exactIterRange 0 = h.rangeCompl :=
  image_id

/--
@isnad1 id=disjoint.1h5v.s5.5fcb7fa37be8 from=translated src=- shape=fc511ff6 vocab=13b1635b
-/
theorem exactIterRange_disjoint_of_ne (h0 : m ≠ n) :
    Disjoint (h.exactIterRange m) (h.exactIterRange n) :=
  disjoint_iff_ne.mpr λ a h1 b h2 ↦ by
    rw [h.mem_exactIterRange_iff] at h1 h2
    rcases h1 with ⟨a, h1, rfl⟩
    rcases h2 with ⟨b, h2, rfl⟩
    exact h.iter_apply_ne_of_mem_rangeCompl_iter_ne h0 h1 h2

/--
@isnad1 id=pairwise.0h4v.s4.fab5154f5205 from=translated src=- shape=24c668f6 vocab=5772beda
-/
theorem exactIterRange_pairwiseDisjoint (S : Set ℕ) :
    S.PairwiseDisjoint h.exactIterRange :=
  λ _ _ _ _ ↦ h.exactIterRange_disjoint_of_ne

/--
@isnad1 id=eq.0h4v.s4.ff1d30c16d18 from=translated src=- shape=665bfb48 vocab=3dd2160e
-/
theorem exactIterRange_card (n : ℕ) :
    (h.exactIterRange n).card = h.rangeCompl.card :=
  h.rangeCompl.card_image_of_injective (h.injective.iterate n)

def iterRangeCompl (n : ℕ) : Finset α := (range n).biUnion h.exactIterRange

/--
@isnad1 id=eq.0h4v.s5.2eb1e06d6cfb from=translated src=- shape=72515eeb vocab=91a9ada8
-/
theorem iterRangeCompl_eq (n : ℕ) :
    h.iterRangeCompl n = (range n).disjiUnion _ (h.exactIterRange_pairwiseDisjoint _) :=
  ((range n).disjiUnion_eq_biUnion _ _).symm

/--
@isnad1 id=eq.0h3v.s4.ae1c847b2b6e from=translated src=- shape=3c191898 vocab=ed6b6c77
-/
theorem iterRangeCompl_zero : h.iterRangeCompl 0 = ∅ := rfl

/--
@isnad1 id=eq.0h4v.s5.04502fe0072d from=translated src=- shape=dc7c71d3 vocab=3e357487
-/
theorem iterRangeCompl_succ (n : ℕ) :
    h.iterRangeCompl n.succ = h.exactIterRange n ∪ h.iterRangeCompl n :=
  (congr_arg₂ _ range_add_one rfl).trans biUnion_insert

/--
@isnad1 id=eq.0h4v.s5.641c331a63a8 from=translated src=- shape=b796e98d vocab=4c97b757
-/
theorem iterRangeCompl_spec :
    ∀ n, (h.iterRangeCompl n : Set α) = (Set.range f^[n])ᶜ
  | 0 => by rw [iterRangeCompl_zero, coe_empty,
              iterate_zero, Set.range_id, Set.compl_univ]
  | n + 1 => by
      rw [h.iterRangeCompl_succ, coe_union, iterRangeCompl_spec n,
        h.exactIterRange_spec, Set.sdiff_eq, Set.inter_union_distrib_right,
        Set.union_compl_self, Set.univ_inter, ← Set.compl_inter]
      exact congrArg _ (Set.inter_eq_left.mpr λ x ⟨y, h1⟩ ↦ ⟨f y, h1⟩)

/--
@isnad1 id=eq.0h3v.s4.64caf8c1ef46 from=translated src=- shape=79d65f8f vocab=7046b518
-/
theorem iterRangeCompl_one : h.iterRangeCompl 1 = h.rangeCompl :=
  (h.iterRangeCompl_succ 0).trans <| (union_empty _).trans h.exactIterRange_zero

/--
@isnad1 id=iff.0h5v.s5.6692283359e9 from=translated src=- shape=c170c9ea vocab=1f0aa3a9
-/
theorem mem_iterRangeCompl_iff : a ∈ h.iterRangeCompl n ↔ a ∉ Set.range f^[n] :=
  Set.ext_iff.mp (h.iterRangeCompl_spec n) a

/--
@isnad1 id=le.0h4v.s5.b97d495e5635 from=translated src=- shape=e1b70ac8 vocab=c12f4b9c
-/
theorem iterRangeCompl_subset_succ (n : ℕ) : h.iterRangeCompl n ⊆ h.iterRangeCompl (n + 1) :=
  h.iterRangeCompl_succ n ▸ subset_union_right

/--
@isnad1 id=le.1h5v.s5.5a546d763c75 from=translated src=- shape=aa26c168 vocab=f7319305
-/
theorem iterRangeCompl_subset_of_le (h0 : m ≤ n) : h.iterRangeCompl m ⊆ h.iterRangeCompl n :=
  Nat.le_induction Subset.rfl (λ n _ h0 ↦ h0.trans (h.iterRangeCompl_subset_succ n)) n h0

/--
@isnad1 id=disjoint.1h5v.s5.cbf24d5c901b from=translated src=- shape=cba4ddc1 vocab=a597f70a
-/
theorem iterRangeCompl_disjoint_exactIterRange (h0 : m ≤ n) :
    Disjoint (h.exactIterRange n) (h.iterRangeCompl m) :=
  (disjoint_biUnion_right _ _ _).mpr
    λ _ h1 ↦ h.exactIterRange_disjoint_of_ne ((mem_range.mp h1).trans_le h0).ne.symm

/--
@isnad1 id=eq.0h4v.s5.7b1955e1bb56 from=translated src=- shape=2059d910 vocab=a4dd863b
-/
theorem iterRangeCompl_card : ∀ n, (h.iterRangeCompl n).card = n * h.rangeCompl.card
  | 0 => card_empty.trans h.rangeCompl.card.zero_mul.symm
  | n + 1 => by
      have h0 := card_union_of_disjoint (h.iterRangeCompl_disjoint_exactIterRange n.le_refl)
      rw [h.iterRangeCompl_succ, h0, h.exactIterRange_card,
        iterRangeCompl_card n, Nat.succ_mul, add_comm]

end Decidable
