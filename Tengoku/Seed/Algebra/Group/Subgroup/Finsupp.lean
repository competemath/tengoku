/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.BigOperators.Finsupp.Basic
public import Tengoku.Seed.Algebra.Group.Subgroup.Lattice

/-! # Connection between `Subgroup.closure` and `Finsupp.prod` -/

public section

assert_not_exists Field

namespace Subgroup

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

/--
@isnad1 id=ex.1h4v.s6.7c86a1c47761 from=seed src=0 shape=928a2fca vocab=219f3f16
-/
@[to_additive]
theorem exists_finsupp_of_mem_closure_range (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι →₀ ℤ, x = a.prod (f · ^ ·) := by
  classical
  induction hx using closure_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp⟩
  | one => use 0; simp
  | mul x y hx hy hx' hy' =>
    obtain ⟨⟨v, rfl⟩, w, rfl⟩ := And.intro hx' hy'
    use v + w
    rw [Finsupp.prod_add_index]
    · simp
    · simp [zpow_add]
  | inv x hx hx' =>
    obtain ⟨a, rfl⟩ := hx'
    use -a
    rw [Finsupp.prod_neg_index]
    · simp
    · simp

/--
@isnad1 id=ex.1h4v.s6.19942115cded from=seed src=0 shape=8a46d72d vocab=363f09b3
-/
@[to_additive]
theorem exists_of_mem_closure_range [Fintype ι] (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι → ℤ, x = ∏ i, f i ^ a i := by
  obtain ⟨a, rfl⟩ := exists_finsupp_of_mem_closure_range f x hx
  exact ⟨a, by simp⟩

variable {f x}

/--
@isnad1 id=iff.0h4v.s6.ca44de31bf73 from=seed src=0 shape=81d0bee3 vocab=219f3f16
-/
@[to_additive]
theorem mem_closure_range_iff :
    x ∈ closure (Set.range f) ↔ ∃ a : ι →₀ ℤ, x = a.prod (f · ^ ·) := by
  refine ⟨exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact Submonoid.prod_mem _ fun i hi ↦ zpow_mem (subset_closure (Set.mem_range_self i)) _

/--
@isnad1 id=iff.0h4v.s6.98d310a99fe0 from=seed src=0 shape=3bae932d vocab=363f09b3
-/
@[to_additive]
theorem mem_closure_range_iff_of_fintype [Fintype ι] :
    x ∈ closure (Set.range f) ↔ ∃ a : ι → ℤ, x = ∏ i, f i ^ a i := by
  rw [Finsupp.equivFunOnFinite.symm.exists_congr_left, mem_closure_range_iff]
  simp

/--
@isnad1 id=iff.0h3v.s6.03c0d3601fda from=seed src=0 shape=02d990d0 vocab=806bdf6c
-/
@[to_additive]
theorem mem_closure_iff_of_fintype {s : Set M} [Fintype s] :
    x ∈ closure s ↔ ∃ a : s → ℤ, x = ∏ i : s, i.1 ^ a i := by
  conv_lhs => rw [← Subtype.range_coe (s := s)]
  exact mem_closure_range_iff_of_fintype

end Subgroup
