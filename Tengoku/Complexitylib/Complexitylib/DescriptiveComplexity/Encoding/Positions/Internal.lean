/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Encoding.Positions.Defs
public import Tengoku

/-!
# Correctness of encoded table positions

The site enumeration is complete, has the expected length, and reproduces the
existing encoder when mapped to table values. These facts justify direct reads.
-/

public section

namespace Complexity.DescriptiveComplexity

/--
@isnad1 id=mem.0h3v.s4.3b33e12fca17 from=translated src=- shape=8b56728a vocab=624ef3c7
-/
theorem mem_encodingTableSites_internal (V : Vocabulary) (card : Nat)
    (site : InputSite V card) : site ∈ encodingTableSites V card := by
  rcases site with ⟨i, args⟩ | ⟨c, a⟩ <;> simp [encodingTableSites, mem_allTuples]

/--
@isnad1 id=eq.0h2v.s6.5c526daa50d1 from=translated src=- shape=d6d0d19f vocab=975f94e4
-/
theorem encodingTableSites_length_internal (V : Vocabulary) (card : Nat) :
    (encodingTableSites V card).length =
      ((List.finRange V.numRels).map (fun i => card ^ V.relArity i)).sum +
        V.numConsts * card := by
  simp [encodingTableSites, List.length_flatMap, allTuples_length]

/--
@isnad1 id=eq.0h2v.s5.f849a3dc1c86 from=translated src=- shape=97968d5b vocab=90ad4dce
-/
theorem map_encodingTableSites_internal {V : Vocabulary} (A : DecFinStruct V) :
    (encodingTableSites V A.card).map (inputSiteValue A) =
      encodeRelsC A ++ encodeConstsC A := by
  simp [encodingTableSites, List.map_flatMap, List.map_map, Function.comp_def,
    inputSiteValue, encodeRelsC, encodeRelC, encodeConstsC, encodeConstC, beq_eq_decide,
    eq_comm]

/--
@isnad1 id=strictmo.0h1v.s3.1bef1c36ce4c from=translated src=- shape=8735051e vocab=2b9f39a1
-/
theorem encodingLength_strictMono_internal (V : Vocabulary) :
    StrictMono (encodingLength V) := by
  intro a b hab
  have hs : ((List.finRange V.numRels).map (fun i => a ^ V.relArity i)).sum ≤
      ((List.finRange V.numRels).map (fun i => b ^ V.relArity i)).sum := by
    generalize List.finRange V.numRels = indices
    induction indices with
    | nil => rfl
    | cons i indices ih =>
      simpa only [List.map_cons, List.sum_cons] using
        Nat.add_le_add (Nat.pow_le_pow_left hab.le (V.relArity i)) ih
  have hc := Nat.mul_le_mul_left V.numConsts hab.le
  unfold encodingLength
  omega

/--
@isnad1 id=nodup.0h2v.s3.d53ed8164241 from=translated src=- shape=a3b7a634 vocab=1440c4a7
-/
theorem encodingTableSites_nodup_internal (V : Vocabulary) (card : Nat) :
    (encodingTableSites V card).Nodup := by
  have hall : (encodingTableSites V card).toFinset = Finset.univ := by
    ext site
    simp [mem_encodingTableSites_internal]
  apply (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (encodingTableSites V card : Multiset (InputSite V card)))).mp
  change (encodingTableSites V card).toFinset.card = (encodingTableSites V card).length
  rw [hall, Finset.card_univ, encodingTableSites_length_internal]
  simp [Fintype.card_sigma, ← List.ofFn_eq_map, List.sum_ofFn]

/--
@isnad1 id=eq.0h3v.s6.2ef630fa0fcc from=translated src=- shape=dede6886 vocab=5b472729
-/
theorem getElem?_encodeStruct_header_internal {V : Vocabulary} (A : DecFinStruct V)
    (i : Fin (A.card + 1)) :
    (encodeStruct A)[i.val]? = some (decide (i.val < A.card)) := by
  rw [encodeStruct]
  by_cases hi : i.val < A.card
  · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hi)]
    simp [hi]
  · have hi' : i.val = A.card := by have := i.isLt; omega
    simp [hi']

end Complexity.DescriptiveComplexity
