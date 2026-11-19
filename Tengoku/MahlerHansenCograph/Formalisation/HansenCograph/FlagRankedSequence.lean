/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.GradedFlagSequence
import Tengoku.Seed.Data.Finset.Sort
import Tengoku.Seed.SetTheory.Cardinal.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rank sequences from finite maximal chains

This file indexes an individual finite maximal chain by its own cardinality.
Unlike `flagEquivRankedFlag`, it needs no grading on the ambient order.  This
lets the product-shuffle construction be applied before a global face-rank
structure has been installed.
-/

namespace HansenCograph

universe u

/-- Maximal chains having exactly `n + 1` elements.-/
abbrev SizedFlag (P : Type u) [LE P] (n : ℕ) :=
  {s : Flag P // Nat.card s = n + 1}

namespace Flag

variable {P : Type u} [PartialOrder P] [BoundedOrder P] [Finite P]

/-- The increasing enumeration of a finite maximal chain of prescribed
cardinality.-/
noncomputable def toRankedFlagOfCardEq (s : Flag P) {n : ℕ}
    (hcard : Nat.card s = n + 1) : RankedFlag P n := by
  classical
  letI : Fintype s := Fintype.ofFinite s
  have hcard' : Fintype.card s = n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let e : Fin (n + 1) ≃o s := Fintype.orderIsoFinOfCardEq s hcard'
  exact
    { toFun := fun k ↦ (e k).1
      map_zero := by
        exact congrArg Subtype.val e.map_bot
      map_last := by
        exact congrArg Subtype.val e.map_top
      covBy_succ := fun k ↦ Flag.coe_covBy_coe.mpr
        ((apply_covBy_apply_iff e).mpr (by
          rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
          rfl)) }

/-- Forgetting the increasing enumeration recovers the original maximal
chain.-/
theorem toFlag_toRankedFlagOfCardEq (s : Flag P) {n : ℕ}
    (hcard : Nat.card s = n + 1) :
    (toRankedFlagOfCardEq s hcard).toFlag = s := by
  apply Flag.ext
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    classical
    letI : Fintype s := Fintype.ofFinite s
    exact (Fintype.orderIsoFinOfCardEq s (by
      simpa only [Nat.card_eq_fintype_card] using hcard) k).2
  · intro hx
    classical
    letI : Fintype s := Fintype.ofFinite s
    let e : Fin (n + 1) ≃o s := Fintype.orderIsoFinOfCardEq s (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩

end Flag

/-- A sized maximal chain embeds into saturated sequences by increasing
enumeration.-/
noncomputable def sizedFlagRankedEmbedding
    {P : Type u} [PartialOrder P] [BoundedOrder P] [Finite P] (n : ℕ) :
    SizedFlag P n ↪ RankedFlag P n where
  toFun s := Flag.toRankedFlagOfCardEq s.1 s.2
  inj' := by
    intro s t h
    apply Subtype.ext
    calc
      s.1 = (Flag.toRankedFlagOfCardEq s.1 s.2).toFlag :=
        (Flag.toFlag_toRankedFlagOfCardEq s.1 s.2).symm
      _ = (Flag.toRankedFlagOfCardEq t.1 t.2).toFlag :=
        congrArg RankedFlag.toFlag h
      _ = t.1 := Flag.toFlag_toRankedFlagOfCardEq t.1 t.2

end HansenCograph
