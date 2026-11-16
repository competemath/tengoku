/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Tengoku.FactorizationTheoryFormalization.FactorizationTheory.Mathlib.Combinatorics.Additive.DavenportConstant
public import Tengoku.Seed.Data.ZMod.Basic

import Tengoku.FactorizationTheoryFormalization.FactorizationTheory.Mathlib.Combinatorics.Additive.DavenportConstant.Prod
import Tengoku.Seed.GroupTheory.SpecificGroups.Cyclic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Davenport constants of cyclic groups

This file computes the Davenport constant of `ZMod n` and, more generally, of every cyclic
additive group. It also specializes the direct-product lower bound to two finite cyclic groups.

## Main results

* `IsAddCyclic.davenportConstant_eq_natCard`: `D(G) = |G|` for a finite cyclic group.
* `IsAddCyclic.davenportConstant_eq_enatCard`: `D(G) = |G|` for every cyclic group, using
  extended cardinality.
* `ZMod.davenportConstant`: `D(ZMod n) = n` when `n ≠ 0`.
* `ZMod.davenportConstant_zero`: `D(ZMod 0) = ⊤`.
* `ZMod.add_sub_one_le_davenportConstant_prod`: the product lower bound for two finite cyclic
  groups.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists Field Ideal

variable {G : Type*}

/-- A finite cyclic additive group has Davenport constant equal to its cardinality.
@isnad1 id=eq.0h1v.s5.809f373a7525 from=translated src=- shape=b8786dde vocab=c64045e5
-/
theorem IsAddCyclic.davenportConstant_eq_natCard
    [AddCommGroup G] [Finite G] [IsAddCyclic G] :
    AddMonoid.davenportConstant G = Nat.card G := by
  apply le_antisymm AddMonoid.davenportConstant_le_natCard
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_ofOrder_eq_natCard (α := G)
  let S := Multiset.replicate (Nat.card G) g
  have hS : S.IsMinimalZeroSum := by
    rw [Multiset.isMinimalZeroSum_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [Multiset.isZeroSum_iff]
      simp [S, ← hg, addOrderOf_nsmul_eq_zero]
    · intro hS0
      have hcard := congrArg Multiset.card hS0
      exact Nat.card_pos.ne' (by simpa [S] using hcard)
    · intro T hT hT0 hTne hTsum
      obtain ⟨k, hkn, rfl⟩ := Multiset.le_replicate_iff.mp hT
      have hk0 : k ≠ 0 := by
        intro hk
        subst k
        simp at hT0
      rw [Multiset.isZeroSum_iff] at hTsum
      simp only [Multiset.sum_replicate] at hTsum
      have hdiv : Nat.card G ∣ k := by
        rw [← hg]
        exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hTsum
      have hcardk : Nat.card G ≤ k :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdiv
      have hk : k = Nat.card G := Nat.le_antisymm hkn hcardk
      exact hTne (by simp [S, hk])
  simpa [S] using hS.card_le_davenportConstant

/-- A cyclic additive group has Davenport constant equal to its extended cardinality.
@isnad1 id=eq.0h1v.s4.157ad84d8f4b from=translated src=- shape=910fa9d2 vocab=9a7e44ed
-/
theorem IsAddCyclic.davenportConstant_eq_enatCard [AddCommGroup G] [IsAddCyclic G] :
    AddMonoid.davenportConstant G = ENat.card G := by
  apply le_antisymm AddMonoid.davenportConstant_le_enatCard
  cases finite_or_infinite G
  · simpa [ENat.card_eq_coe_natCard] using
      IsAddCyclic.davenportConstant_eq_natCard (G := G).ge
  · rw [ENat.card_eq_top_of_infinite, top_le_iff, ENat.eq_top_iff_forall_ge]
    intro n
    obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := G)
    have hgord : addOrderOf g = 0 :=
      Infinite.addOrderOf_eq_zero_of_forall_mem_zmultiples hg
    have hginj : Function.Injective (fun k : ℕ ↦ k • g) := by
      rw [injective_nsmul_iff_not_isOfFinAddOrder, ← addOrderOf_eq_zero_iff]
      exact hgord
    let S := Multiset.replicate n g
    have hfree : S.IsZeroSumFree := by
      rw [Multiset.isZeroSumFree_iff]
      intro T hT hT0 hTsum
      obtain ⟨k, -, rfl⟩ := Multiset.le_replicate_iff.mp hT
      rw [Multiset.isZeroSum_iff] at hTsum
      have hk : k = 0 := hginj (by simpa using hTsum)
      subst k
      exact hT0 rfl
    have hbound := hfree.isMinimalZeroSum_cons_neg_sum.card_le_davenportConstant
    exact le_trans (ENat.natCast_le_natCast.mpr (Nat.le_succ n))
      (by simpa [S] using hbound)

/-- The Davenport constant of `ZMod n` is `n` when `n` is nonzero.
@isnad1 id=eq.1h1v.s4.5686c1e3c345 from=translated src=- shape=b84d43ff vocab=c44def33
-/
@[simp]
protected theorem ZMod.davenportConstant {n : ℕ} (hn : n ≠ 0) :
    AddMonoid.davenportConstant (ZMod n) = n := by
  let _ : NeZero n := ⟨hn⟩
  let _ : IsAddCyclic ℤ :=
    ⟨1, fun k ↦ ⟨k, by simp only [smul_eq_mul, mul_one]⟩⟩
  let _ : IsAddCyclic (ZMod n) :=
    isAddCyclic_of_surjective (Int.castRingHom _) ZMod.intCast_surjective
  simpa using IsAddCyclic.davenportConstant_eq_natCard (G := ZMod n)

/-- The infinite cyclic group `ZMod 0` has infinite Davenport constant.
@isnad1 id=eq.0h0v.s5.97c14ae05def from=translated src=- shape=4d120df5 vocab=31259155
-/
@[simp]
theorem ZMod.davenportConstant_zero : AddMonoid.davenportConstant (ZMod 0) = ⊤ := by
  let _ : IsAddCyclic ℤ :=
    ⟨1, fun k ↦ ⟨k, by simp only [smul_eq_mul, mul_one]⟩⟩
  let _ : IsAddCyclic (ZMod 0) :=
    isAddCyclic_of_surjective (Int.castRingHom _) ZMod.intCast_surjective
  rw [IsAddCyclic.davenportConstant_eq_enatCard,
    ENat.card_eq_top_of_infinite]

/-- For nonzero `m` and `n`, `m + n - 1 ≤ D(ZMod m × ZMod n)`.
@isnad1 id=le.2h2v.s6.d26177da0be7 from=translated src=- shape=ef6c320f vocab=bdc0350d
-/
theorem ZMod.add_sub_one_le_davenportConstant_prod {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) :
    (m : ℕ∞) + n - 1 ≤ AddMonoid.davenportConstant (ZMod m × ZMod n) := by
  simpa [ZMod.davenportConstant hm, ZMod.davenportConstant hn] using
    (AddMonoid.add_sub_one_le_davenportConstant_prod (G := ZMod m) (H := ZMod n))
