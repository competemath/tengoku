/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Tengoku

/-!
# LeanPool.ABCExceptions.ForMathlib.Misc
-/

@[expose] public section

noncomputable section

open Set

variable {d : ℕ}

-- TODO (BM): move everything in this section to mathlib
section

/--
@isnad1 id=eq.0h1v.s4.70e20abb397a from=translated src=- shape=3ad823b4 vocab=1238d3a7
-/
lemma Nat.Iic_eq_Icc (n : ℕ) : Finset.Iic n = Finset.Icc 0 n := by simp [Finset.Iic_eq_Icc]

/--
@isnad1 id=eq.2h4v.s6.f40047a30a51 from=translated src=- shape=b81ccafe vocab=d295405e
-/
theorem Finset.Ico_union_Icc_eq_Icc {α : Type*} [LinearOrder α]
    [LocallyFiniteOrder α] {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    Ico a b ∪ Icc b c = Icc a c := by
  simp [← Finset.coe_inj, Set.Ico_union_Icc_eq_Icc h₁ h₂]

/--
@isnad1 id=eq.2h4v.s7.e7d5d9f134f9 from=translated src=- shape=cde9a55d vocab=a6706730
-/
theorem Finset.Ico_union_Icc_eq_Icc' {α : Type*} [LinearOrder α]
    [Add α] [One α] [SuccAddOrder α]
    [LocallyFiniteOrder α] {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c + 1) :
    Finset.Ico a b ∪ Finset.Icc b c = Finset.Icc a c := by
  ext i
  simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Icc]
  constructor
  · rintro (⟨h₃, h₄⟩ | ⟨h₃, h₄⟩)
    · exact ⟨h₃, Order.le_of_lt_add_one (h₄.trans_le h₂)⟩
    · exact ⟨h₁.trans h₃, h₄⟩
  · rintro ⟨h₃, h₄⟩
    obtain h₅ | h₅ := lt_or_ge i b
    · exact Or.inl ⟨h₃, h₅⟩
    · exact Or.inr ⟨h₅, h₄⟩

/--
@isnad1 id=eq.2h3v.s5.0f6d426b365d from=translated src=- shape=baaf0cb7 vocab=7390468f
-/
theorem Nat.Icc_union_Icc_eq_Icc {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    Finset.Icc a b ∪ Finset.Icc (b + 1) c = Finset.Icc a c := by
  ext i
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

/--
@isnad1 id=eq.1h4v.s6.bcf3198d7037 from=translated src=- shape=fcfb8764 vocab=babe0906
-/
@[to_additive]
theorem Finset.prod_Icc_succ_bot {M : Type*} [CommMonoid M] {a b : ℕ}
    (hab : a ≤ b) (f : ℕ → M) :
    (∏ k ∈ Icc a b, f k) = f a * (∏ k ∈ Icc (a + 1) b, f k) := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hab, prod_insert]
  simp

/--
@isnad1 id=finite.0h1v.s4.64a09a61eaf8 from=translated src=- shape=006cad5f vocab=4c06c529
-/
lemma Finset.finite_subsets (s : Finset ℕ) : {a | a ⊆ s}.Finite := by
  rw [show {a : Finset ℕ | a ⊆ s} = (s.powerset : Set (Finset ℕ)) by
    ext a
    simp]
  exact s.powerset.finite_toSet

/--
@isnad1 id=eq.1h4v.s6.4d2aa66cd9cb from=translated src=- shape=5dd4fd1d vocab=c48ef2b3
-/
@[to_additive]
lemma prod_Icc_eq_prod_range_mul_prod_Icc {α : Type*} [CommMonoid α] {f : ℕ → α} {t : ℕ}
    (ht : t ≤ d + 1) :
    ∏ i ≤ d, f i = (∏ i ∈ Finset.range t, f i) * ∏ i ∈ Finset.Icc t d, f i := by
  rw [Nat.Iic_eq_Icc, ← Finset.Ico_union_Icc_eq_Icc' (Nat.zero_le t) ht, Nat.Ico_zero_eq_range,
    Finset.prod_union]
  simp +contextual [Finset.disjoint_left]

/--
@isnad1 id=eq.0h3v.s7.06e706b66cf9 from=translated src=- shape=87994888 vocab=5de5ec9a
-/
lemma Iic_sdiff_Icc_eq_inter {α : Type*} [LinearOrder α]
    [LocallyFiniteOrder α] [LocallyFiniteOrderBot α] {x y : α} :
    Finset.Iic x \ Finset.Icc y x = Finset.Iic x ∩ Finset.Iio y := by
  ext a; simp +contextual [- not_and]

/--
@isnad1 id=eq.1h3v.s6.6a85654d37cf from=translated src=- shape=529affde vocab=d7162ca7
-/
lemma Iic_sdiff_Icc_of_le {α : Type*} [LinearOrder α]
    [LocallyFiniteOrder α] [LocallyFiniteOrderBot α] {x y : α} (h : y ≤ x) :
    Finset.Iic x \ Finset.Icc y x = Finset.Iio y := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_Icc, Finset.mem_Iio]
  constructor
  · rintro ⟨hax, hnot⟩
    exact lt_of_not_ge fun hya ↦ hnot ⟨hya, hax⟩
  · intro hay
    exact ⟨hay.le.trans h, fun hyx ↦ not_le_of_gt hay hyx.1⟩

end
