import Tengoku.Seed.Order.Partition.Finpartition
import Tengoku.Seed.Data.Finset.Lattice.Fold
import Tengoku.Seed.Data.Finset.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite partitions from indexed set covers

An indexed disjoint cover may contain empty or repeated sets. The construction
keeps exactly the distinct nonempty members and provides their enumeration.
-/

set_option autoImplicit false

open Set

noncomputable section

namespace Tiling.Combinatorics.FiniteSetPartitions

variable {α : Type*}

/-- Enumerate each member of a finite set exactly once.-/
def enumerate (parts : Finset (Set α)) : Fin parts.card → Set α :=
  fun i => (parts.equivFin.symm i : Set α)

/--
@isnad1 id=mem.0h3v.s5.77ae91cee978 from=translated src=- shape=759d94d5 vocab=f7e42118
-/
theorem enumerate_mem (parts : Finset (Set α)) (i : Fin parts.card) :
    enumerate parts i ∈ parts :=
  (parts.equivFin.symm i).property

/--
@isnad1 id=injectiv.0h2v.s4.cdf7896c6b5f from=translated src=- shape=dbad006b vocab=843c0b68
-/
theorem enumerate_injective (parts : Finset (Set α)) :
    Function.Injective (enumerate parts) := by
  intro i j h
  exact parts.equivFin.symm.injective (Subtype.ext h)

/--
@isnad1 id=eq.0h2v.s5.3c902ffb1f90 from=translated src=- shape=6cb1c263 vocab=888f95ee
-/
theorem iUnion_enumerate (parts : Finset (Set α)) :
    (⋃ i, enumerate parts i) = ⋃₀ parts := by
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    exact Set.mem_sUnion.mpr ⟨enumerate parts i, enumerate_mem parts i, hx⟩
  · rintro ⟨S, hS, hx⟩
    apply Set.mem_iUnion.mpr
    refine ⟨parts.equivFin ⟨S, hS⟩, ?_⟩
    simpa [enumerate] using hx

/-- Keep the distinct nonempty members of an indexed family.-/
def nonemptyPieces {n : ℕ} (part : Fin n → Set α) : Finset (Set α) := by
  classical
  exact (Finset.univ.image part).filter Set.Nonempty

/--
@isnad1 id=iff.0h4v.s5.e8f90ff853cb from=translated src=- shape=e1df9bfe vocab=7c215075
-/
theorem mem_nonemptyPieces {n : ℕ} (part : Fin n → Set α) (S : Set α) :
    S ∈ nonemptyPieces part ↔ (∃ i, part i = S) ∧ S.Nonempty := by
  classical
  simp [nonemptyPieces]

/--
@isnad1 id=eq.0h3v.s5.d55522c8c297 from=translated src=- shape=2ac660c6 vocab=15abfbe2
-/
theorem sUnion_nonemptyPieces {n : ℕ} (part : Fin n → Set α) :
    ⋃₀ (nonemptyPieces part) = ⋃ i, part i := by
  classical
  ext x
  constructor
  · rintro ⟨S, hS, hx⟩
    obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_sUnion.mpr ⟨part i,
      (mem_nonemptyPieces part (part i)).mpr ⟨⟨i, rfl⟩, ⟨x, hxi⟩⟩, hxi⟩

/--
@isnad1 id=pairwise.1h3v.s6.6c5c99d81ba0 from=translated src=- shape=84fe6a8d vocab=fce9838e
-/
theorem pairwiseDisjoint_nonemptyPieces {n : ℕ} (part : Fin n → Set α)
    (hdis : Set.PairwiseDisjoint Set.univ part) :
    (nonemptyPieces part : Set (Set α)).PairwiseDisjoint id := by
  classical
  intro S hS U hU hne
  obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
  obtain ⟨⟨j, rfl⟩, _⟩ := (mem_nonemptyPieces part U).mp hU
  exact hdis (Set.mem_univ _) (Set.mem_univ _) (fun hij => hne (congrArg part hij))

/--
@isnad1 id=eq.1h4v.s6.5b7b1aa5ee77 from=translated src=- shape=a97dd071 vocab=b93ba5d6
-/
theorem sup_nonemptyPieces {A : Set α} {n : ℕ} (part : Fin n → Set α)
    (hcover : (⋃ i, part i) = A) :
    (nonemptyPieces part).sup id = A := by
  classical
  calc
    (nonemptyPieces part).sup id = ⋃₀ (nonemptyPieces part) :=
      Finset.sup_id_set_eq_sUnion _
    _ = ⋃ i, part i := sUnion_nonemptyPieces part
    _ = A := hcover

/-- An indexed disjoint cover gives a canonical finite partition.-/
def finpartitionOfIndexed {A : Set α} {n : ℕ} (part : Fin n → Set α)
    (hdis : Set.PairwiseDisjoint Set.univ part) (hcover : (⋃ i, part i) = A) :
    Finpartition A := by
  classical
  exact (Finpartition.ofPairwiseDisjoint (nonemptyPieces part)
    (pairwiseDisjoint_nonemptyPieces part hdis)).copy (sup_nonemptyPieces part hcover)

/--
@isnad1 id=eq.2h4v.s6.e365abf3dead from=translated src=- shape=7285325a vocab=bbe06c09
-/
theorem finpartitionOfIndexed_parts {A : Set α} {n : ℕ}
    (part : Fin n → Set α) (hdis : Set.PairwiseDisjoint Set.univ part)
    (hcover : (⋃ i, part i) = A) :
    (finpartitionOfIndexed part hdis hcover).parts = nonemptyPieces part := by
  classical
  simp [finpartitionOfIndexed, Finpartition.ofPairwiseDisjoint,
    Finset.erase_eq_of_notMem, mem_nonemptyPieces]

/--
@isnad1 id=nonempty.1h4v.s6.c4c3c9e36a92 from=translated src=- shape=8c17323d vocab=d33881bf
-/
theorem finpartitionParts_nonempty {A : Set α} (P : Finpartition A)
    (S : Set α) (hS : S ∈ P.parts) : S.Nonempty := by
  exact Set.nonempty_iff_ne_empty.mpr (P.ne_bot hS)

end Tiling.Combinatorics.FiniteSetPartitions
