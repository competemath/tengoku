/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Valuation.ValuationSubring
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residue characteristic under pullback of a valuation subring

A field embedding preserves the nonunit condition for the pulled-back
valuation subring. Consequently equality of integer residues downstairs
implies equality upstairs, so residue characteristic zero descends.
No algebraicity, Henselianity, or rank assumption is used.
-/

namespace ValuationSubring

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]

/-- The actual field embedding preserves and reflects nonunits of a
pulled-back valuation subring.
@isnad1 id=iff.0h5v.s7.a3fb00a7f70d from=translated src=- shape=4c39380b vocab=dc9359c5
-/
theorem mem_nonunits_comap_iff (A : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  rw [mem_nonunits_iff_or, mem_nonunits_iff_or]
  constructor
  · rintro (rfl | hx)
    · exact Or.inl (map_zero f)
    · exact Or.inr (by simpa only [map_inv₀, mem_comap] using hx)
  · rintro (hx | hx)
    · exact Or.inl (f.injective (hx.trans (map_zero f).symm))
    · exact Or.inr (by simpa only [map_inv₀, mem_comap] using hx)

/-- Residue characteristic zero descends along any field embedding by
pulling back the specified valuation subring.
@isnad1 id=charzero.0h4v.s8.af7b48a9a1eb from=translated src=- shape=796a5e14 vocab=7d04a16f
-/
theorem charZero_residueField_comap (A : ValuationSubring L) (f : K →+* L)
    [CharZero (IsLocalRing.ResidueField A)] :
    CharZero (IsLocalRing.ResidueField (A.comap f)) := by
  constructor
  intro m n hmn
  have hres : IsLocalRing.residue (A.comap f) (m : A.comap f) =
      IsLocalRing.residue (A.comap f) (n : A.comap f) := by
    simpa only [map_natCast] using hmn
  have hmax : (m : A.comap f) - (n : A.comap f) ∈
      IsLocalRing.maximalIdeal (A.comap f) :=
    (ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal
        (m : A.comap f) (n : A.comap f)).mp hres
  have hnonunit : (m : K) - (n : K) ∈ (A.comap f).nonunits :=
    (A.comap f).coe_mem_nonunits_iff.mpr hmax
  have hnonunit' : f ((m : K) - (n : K)) ∈ A.nonunits :=
    (mem_nonunits_comap_iff A f ((m : K) - (n : K))).mp hnonunit
  rw [map_sub, map_natCast, map_natCast] at hnonunit'
  have hmax' : (m : A) - (n : A) ∈ IsLocalRing.maximalIdeal A :=
    A.coe_mem_nonunits_iff.mp hnonunit'
  have hres' : IsLocalRing.residue A (m : A) = IsLocalRing.residue A (n : A) :=
    (ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal
      (m : A) (n : A)).mpr hmax'
  have hcast : (m : IsLocalRing.ResidueField A) = (n : IsLocalRing.ResidueField A) := by
    simpa only [map_natCast] using hres'
  exact Nat.cast_injective hcast

end ValuationSubring
