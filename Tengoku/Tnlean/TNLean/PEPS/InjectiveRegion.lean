/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Data.Finset.Basic
import Tengoku.Seed.Data.Finset.SDiff
import Tengoku.Seed.Data.Finset.Union
import Tengoku.Seed.Data.Fintype.Basic
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Region decompositions for PEPS injectivity arguments

The finite-region decomposition used in the proof that the union of two
injective PEPS regions is injective consists of four canonical parts.

For two regions \(A\) and \(B\), the source proof partitions the vertex set into
four parts:

* \(A \setminus B\),
* \(A \cap B\),
* \(B \setminus A\),
* \((A \cup B)^c\).

The elementary identities below are used in the tensor-level proof of the
injective-union lemma.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma lem:injective_union](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [DecidableEq V]

/-! ### Four-region decomposition for two finite regions -/

/-- An abstract predicate assigning injectivity to finite vertex regions.

This is the region-level injectivity hypothesis used in the normal PEPS
blocking argument of arXiv:1804.04964, Section 3.  It is distinct from
one-vertex injectivity, since the source proof applies injectivity to blocked
regions such as \(R\), \(S\), \(T\), and their complements.
Source: arXiv:1804.04964, Section 3, lines 1407--1545 of
`Papers/1804.04964/paper_normal.tex`.-/
structure RegionInjectivityData (V : Type*) where
  /-- The assertion that a finite vertex region is injective after blocking.-/
  IsInjective : Finset V → Prop

/-- The union-closure assertion for region injectivity.

This is the formal hypothesis supplied by the tensor-level
union-of-injective-regions lemma.  It is recorded separately so later
coordinate arguments may use the source lemma without repeating its proof.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404 of `Papers/1804.04964/paper_normal.tex`.-/
structure RegionInjectivityUnionClosure (κ : RegionInjectivityData V) : Prop where
  /-- The union of two injective finite vertex regions is injective.-/
  union_injective :
    ∀ {A B : Finset V}, κ.IsInjective A → κ.IsInjective B → κ.IsInjective (A ∪ B)

/-- A nonempty finite union of injective regions is injective under union closure.

This is the finite iteration of the source lemma used when the displayed
regions \(R\), \(S\), and \(T\) are described as unions of smaller injective
rectangles.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and the
examples following it, lines 1322--1430 of
`Papers/1804.04964/paper_normal.tex`.
@isnad1 id=isinject.3h5v.s5.46397f3e131c from=translated src=- shape=74ebb1a2 vocab=577859fd
-/
theorem RegionInjectivityUnionClosure.biUnion_injective
    {ι : Type*} {κ : RegionInjectivityData V} (hUnion : RegionInjectivityUnionClosure κ)
    {s : Finset ι} (hs : s.Nonempty) (R : ι → Finset V)
    (hR : ∀ i ∈ s, κ.IsInjective (R i)) :
    κ.IsInjective (s.biUnion R) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa using hR i (by simp)
  | cons i s hi _ ih =>
      rw [Finset.cons_eq_insert, Finset.biUnion_insert]
      exact hUnion.union_injective (hR i (by simp)) (ih fun j hj => hR j (by simp [hj]))

/-- A finite union of injective regions with at least one nonempty member is injective under
union closure, with the injectivity required only of the nonempty members.

This is the variant of the finite iteration of the source lemma used when a rectangular
cover lists pieces that may degenerate to the empty region (a band of zero width at the
torus seam): the empty pieces contribute nothing to the union and need no injectivity.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and the examples following
it, lines 1322--1430 of `Papers/1804.04964/paper_normal.tex`.
@isnad1 id=isinject.3h5v.s6.ee28a209d843 from=translated src=- shape=63734d90 vocab=577859fd
-/
theorem RegionInjectivityUnionClosure.biUnion_injective_of_nonempty
    {ι : Type*} {κ : RegionInjectivityData V} (hUnion : RegionInjectivityUnionClosure κ)
    {s : Finset ι} (R : ι → Finset V)
    (hne : ∃ i ∈ s, (R i).Nonempty)
    (hR : ∀ i ∈ s, (R i).Nonempty → κ.IsInjective (R i)) :
    κ.IsInjective (s.biUnion R) := by
  classical
  have heq : s.biUnion R = (s.filter fun i => (R i).Nonempty).biUnion R := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    exact ⟨fun ⟨i, hi, hv⟩ => ⟨i, ⟨hi, ⟨v, hv⟩⟩, hv⟩, fun ⟨i, ⟨hi, _⟩, hv⟩ => ⟨i, hi, hv⟩⟩
  obtain ⟨i, hi, hne'⟩ := hne
  rw [heq]
  exact hUnion.biUnion_injective ⟨i, Finset.mem_filter.mpr ⟨hi, hne'⟩⟩ R fun j hj =>
    hR j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2

/-- The part of the left region outside the right region.-/
def regionOnlyLeft (A B : Finset V) : Finset V :=
  A \ B

/-- The overlap of two regions.-/
def regionOverlap (A B : Finset V) : Finset V :=
  A ∩ B

/-- The part of the right region outside the left region.-/
def regionOnlyRight (A B : Finset V) : Finset V :=
  B \ A

/-- The complement of the union of two regions.-/
def regionOutsideUnion [Fintype V] (A B : Finset V) : Finset V :=
  Finset.univ \ (A ∪ B)

/-- The complement of a finite region in the ambient vertex set.-/
def regionComplement [Fintype V] (R : Finset V) : Finset V :=
  Finset.univ \ R

/--
@isnad1 id=iff.0h4v.s5.d36362229b4f from=translated src=- shape=615e9d3a vocab=2591001b
-/
@[simp] theorem mem_regionOnlyLeft (A B : Finset V) (v : V) :
    v ∈ regionOnlyLeft A B ↔ v ∈ A ∧ v ∉ B := by
  simp [regionOnlyLeft]

/--
@isnad1 id=iff.0h4v.s5.0381b0501c3c from=translated src=- shape=6ecb9a81 vocab=a0259714
-/
@[simp] theorem mem_regionOverlap (A B : Finset V) (v : V) :
    v ∈ regionOverlap A B ↔ v ∈ A ∧ v ∈ B := by
  simp [regionOverlap]

/--
@isnad1 id=iff.0h4v.s5.db9c72e9d7c4 from=translated src=- shape=1b998038 vocab=3a36540a
-/
@[simp] theorem mem_regionOnlyRight (A B : Finset V) (v : V) :
    v ∈ regionOnlyRight A B ↔ v ∈ B ∧ v ∉ A := by
  simp [regionOnlyRight]

/--
@isnad1 id=iff.0h4v.s5.606329567280 from=translated src=- shape=506cff20 vocab=a4daece4
-/
@[simp] theorem mem_regionOutsideUnion [Fintype V] (A B : Finset V) (v : V) :
    v ∈ regionOutsideUnion A B ↔ v ∉ A ∧ v ∉ B := by
  simp [regionOutsideUnion, not_or]

/--
@isnad1 id=iff.0h3v.s5.3905209dd8a6 from=translated src=- shape=e9e15701 vocab=d9ee62d9
-/
@[simp] theorem mem_regionComplement [Fintype V] (R : Finset V) (v : V) :
    v ∈ regionComplement R ↔ v ∉ R := by
  simp [regionComplement]

/-- The outside block in the four-region decomposition is the complement of
`A ∪ B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the fourth region in the blocked proof is written as
`(A ∪ B)ᶜ`.
@isnad1 id=eq.0h3v.s5.44476ceb162c from=translated src=- shape=11c9820e vocab=b6d507e2
-/
theorem regionOutsideUnion_eq_regionComplement_union [Fintype V]
    (A B : Finset V) :
    regionOutsideUnion A B = regionComplement (A ∪ B) := by
  rfl

/-- The left-only and overlap regions reconstruct the left region.
@isnad1 id=eq.0h3v.s4.1bebf57f1edb from=translated src=- shape=4ce1cd19 vocab=75f099b1
-/
theorem regionOnlyLeft_union_overlap (A B : Finset V) :
    regionOnlyLeft A B ∪ regionOverlap A B = A := by
  simpa [regionOnlyLeft, regionOverlap] using Finset.sdiff_union_inter A B

/-- The overlap and right-only regions reconstruct the right region.
@isnad1 id=eq.0h3v.s4.9357e2748864 from=translated src=- shape=f5a9fd49 vocab=b0551fae
-/
theorem regionOverlap_union_onlyRight (A B : Finset V) :
    regionOverlap A B ∪ regionOnlyRight A B = B := by
  simpa [regionOverlap, regionOnlyRight, Finset.union_comm, Finset.inter_comm] using
    Finset.sdiff_union_inter B A

/-- The three regions inside `A ∪ B` reconstruct the union.
@isnad1 id=eq.0h3v.s5.08e162b0eacc from=translated src=- shape=45225792 vocab=d01de4cc
-/
theorem regionThreePart_union (A B : Finset V) :
    regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B = A ∪ B := by
  calc
    regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B =
        A ∪ regionOnlyRight A B := by rw [regionOnlyLeft_union_overlap]
    _ = A ∪ B := by
      simp [regionOnlyRight, Finset.union_sdiff_self_eq_union]

/-- The four regions form a decomposition of the whole finite vertex set.
@isnad1 id=eq.0h3v.s5.019571ad2b91 from=translated src=- shape=94a542d4 vocab=50c29e30
-/
theorem regionFourPart_union [Fintype V] (A B : Finset V) :
    regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B ∪
      regionOutsideUnion A B = Finset.univ := by
  calc
    regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B ∪
        regionOutsideUnion A B =
        (A ∪ B) ∪ (Finset.univ \ (A ∪ B)) := by
          rw [regionThreePart_union, regionOutsideUnion]
    _ = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ (A ∪ B))

/-- Every vertex belongs to one of the four regions in the decomposition.
@isnad1 id=or.0h4v.s6.ee79e2c6130f from=translated src=- shape=332251a4 vocab=f5a162bf
-/
theorem regionFourPart_cases [Fintype V] (A B : Finset V) (v : V) :
    v ∈ regionOnlyLeft A B ∨ v ∈ regionOverlap A B ∨
      v ∈ regionOnlyRight A B ∨ v ∈ regionOutsideUnion A B := by
  by_cases hvA : v ∈ A
  · by_cases hvB : v ∈ B
    · exact Or.inr <| Or.inl <| by simp [regionOverlap, hvA, hvB]
    · exact Or.inl <| by simp [regionOnlyLeft, hvA, hvB]
  · by_cases hvB : v ∈ B
    · exact Or.inr <| Or.inr <| Or.inl <| by simp [regionOnlyRight, hvA, hvB]
    · exact Or.inr <| Or.inr <| Or.inr <| by
        simp [regionOutsideUnion, hvA, hvB]

/-- The four regions, indexed in the order
\(A\setminus B\), \(A\cap B\), \(B\setminus A\), \((A\cup B)^c\).-/
def regionUnionPart [Fintype V] (A B : Finset V) (i : Fin 4) : Finset V :=
  if i = 0 then
    regionOnlyLeft A B
  else if i = 1 then
    regionOverlap A B
  else if i = 2 then
    regionOnlyRight A B
  else
    regionOutsideUnion A B

/--
@isnad1 id=eq.0h3v.s5.5cf5ee7f50b2 from=translated src=- shape=1e1e3b97 vocab=965b87ef
-/
@[simp] theorem regionUnionPart_zero [Fintype V] (A B : Finset V) :
    regionUnionPart A B 0 = regionOnlyLeft A B := by
  simp [regionUnionPart]

/--
@isnad1 id=eq.0h3v.s5.a04d96359c32 from=translated src=- shape=1e1e3b97 vocab=f528047b
-/
@[simp] theorem regionUnionPart_one [Fintype V] (A B : Finset V) :
    regionUnionPart A B 1 = regionOverlap A B := by
  simp [regionUnionPart]

/--
@isnad1 id=eq.0h3v.s5.5f7564fccfe7 from=translated src=- shape=1e1e3b97 vocab=a93146a5
-/
@[simp] theorem regionUnionPart_two [Fintype V] (A B : Finset V) :
    regionUnionPart A B 2 = regionOnlyRight A B := by
  simp [regionUnionPart]

/--
@isnad1 id=eq.0h3v.s5.57db13542a8f from=translated src=- shape=1e1e3b97 vocab=9db3d75d
-/
@[simp] theorem regionUnionPart_three [Fintype V] (A B : Finset V) :
    regionUnionPart A B 3 = regionOutsideUnion A B := by
  simp [regionUnionPart, show (3 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide]

/-- The fourth indexed region is the complement of `A ∪ B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the tensor called `X` is attached to `(A ∪ B)ᶜ`, the fourth
piece of the blocked four-region picture.
@isnad1 id=eq.0h3v.s5.5b5fc4566f4e from=translated src=- shape=0a00f155 vocab=abeeaa22
-/
theorem regionUnionPart_three_eq_regionComplement_union [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 3 = regionComplement (A ∪ B) := by
  rw [regionUnionPart_three, regionOutsideUnion_eq_regionComplement_union]

/-- The first two indexed regions reconstruct `A`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the source proof identifies `A` with the union of
`A \ B` and `A ∩ B` before applying injectivity of `A`.
@isnad1 id=eq.0h3v.s6.662cdc9a8386 from=translated src=- shape=ac6fdd24 vocab=49d0063f
-/
theorem regionUnionPart_zero_union_one [Fintype V] (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 1 = A := by
  simpa using regionOnlyLeft_union_overlap A B

/-- The subfamily of indexed regions `0,1` reconstructs `A`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the first inverse is applied to
\(A=(A\setminus B)\cup(A\cap B)\).
@isnad1 id=eq.0h3v.s6.c965b8a55c28 from=translated src=- shape=d5d74991 vocab=0e8695e5
-/
theorem regionUnionPart_biUnion_zero_one [Fintype V] (A B : Finset V) :
    ({0, 1} : Finset (Fin 4)).biUnion (regionUnionPart A B) = A := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion] using
    regionUnionPart_zero_union_one A B

/-- The middle two indexed regions reconstruct `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap tensor, the source proof identifies
`B` with the union of `A ∩ B` and `B \ A`.
@isnad1 id=eq.0h3v.s6.86f349eb0433 from=translated src=- shape=b44d393d vocab=49d0063f
-/
theorem regionUnionPart_one_union_two [Fintype V] (A B : Finset V) :
    regionUnionPart A B 1 ∪ regionUnionPart A B 2 = B := by
  simpa using regionOverlap_union_onlyRight A B

/-- The subfamily of indexed regions `1,2` reconstructs `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap tensor, the second inverse is
applied to \(B=(A\cap B)\cup(B\setminus A)\).
@isnad1 id=eq.0h3v.s6.a287d22fec78 from=translated src=- shape=dbc5b74a vocab=0e8695e5
-/
theorem regionUnionPart_biUnion_one_two [Fintype V] (A B : Finset V) :
    ({1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B) = B := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion] using
    regionUnionPart_one_union_two A B

/-- The first three indexed regions reconstruct `A ∪ B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the region whose injectivity is being proved is the union of the
three inside parts of the four-region decomposition.
@isnad1 id=eq.0h3v.s6.e5e182919ef3 from=translated src=- shape=04977bd1 vocab=49d0063f
-/
theorem regionUnionPart_zero_union_one_union_two [Fintype V] (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 1 ∪ regionUnionPart A B 2 =
      A ∪ B := by
  simpa using regionThreePart_union A B

/-- The subfamily of indexed regions `0,1,2` reconstructs `A ∪ B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the injectivity conclusion is for the union of the three inside
indexed regions.
@isnad1 id=eq.0h3v.s7.46854f905596 from=translated src=- shape=db23c385 vocab=12ffb98d
-/
theorem regionUnionPart_biUnion_zero_one_two [Fintype V] (A B : Finset V) :
    ({0, 1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B) = A ∪ B := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion, Finset.union_assoc] using
    regionUnionPart_zero_union_one_union_two A B

/-- Convenience form of `Finset.singleton_biUnion` for the outside indexed
region.
@isnad1 id=eq.0h3v.s6.726024e984c8 from=translated src=- shape=85394a03 vocab=d35ecf7d
-/
theorem regionUnionPart_biUnion_three [Fintype V] (A B : Finset V) :
    ({3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionUnionPart A B 3 := by
  rw [Finset.singleton_biUnion]

/-- The selected subfamily `3` is the complement of the selected inside
subfamily `0,1,2`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the proof starts with the three inside indexed blocks and a
boundary tensor on their complement.
@isnad1 id=eq.0h3v.s7.f47ac1b50367 from=translated src=- shape=3cc39243 vocab=dd546a9f
-/
theorem regionUnionPart_biUnion_three_eq_regionComplement_zero_one_two [Fintype V]
    (A B : Finset V) :
    ({3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement (({0, 1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_three, regionUnionPart_biUnion_zero_one_two,
    regionUnionPart_three_eq_regionComplement_union]

/-- The fourth indexed region is the intersection of the complements of `A`
and `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after injectivity of `A` and then `B` are applied, the remaining
tensor is supported on the outside region \((A \cup B)^c=A^c\cap B^c\).
@isnad1 id=eq.0h3v.s5.efdf5d72f43a from=translated src=- shape=aece6ccc vocab=8519ddae
-/
theorem regionUnionPart_three_eq_regionComplement_left_inter_right [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 3 = regionComplement A ∩ regionComplement B := by
  ext v
  simp [regionComplement]

/-- The right-only indexed region together with the outside region reconstructs
the complement of `A`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after applying injectivity of `A`, the remaining diagram contains
the `B \ A` block and the outside block.
@isnad1 id=eq.0h3v.s6.c96ebe0ee8d8 from=translated src=- shape=426dcec1 vocab=abeeaa22
-/
theorem regionUnionPart_two_union_three_eq_regionComplement_left [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 2 ∪ regionUnionPart A B 3 = regionComplement A := by
  ext v
  simp only [regionUnionPart_two, regionUnionPart_three, Finset.mem_union,
    mem_regionOnlyRight, mem_regionOutsideUnion, mem_regionComplement]
  tauto

/-- The indexed subfamily `2,3` reconstructs the complement of `A`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after injectivity of `A` is applied, the remaining diagram is
carried by `B \ A` and the outside block.
@isnad1 id=eq.0h3v.s6.2f0f5b16d753 from=translated src=- shape=229bd0e6 vocab=dd546a9f
-/
theorem regionUnionPart_biUnion_two_three_eq_regionComplement_left [Fintype V]
    (A B : Finset V) :
    ({2, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement A := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion] using
    regionUnionPart_two_union_three_eq_regionComplement_left A B

/-- The selected subfamily `2,3` is the complement of the selected subfamily
`0,1`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after applying injectivity of \(A\), the remaining indexed blocks
are precisely the complement of the two blocks forming \(A\).
@isnad1 id=eq.0h3v.s7.d43e3a64eedf from=translated src=- shape=3e3af074 vocab=dd546a9f
-/
theorem regionUnionPart_biUnion_two_three_eq_regionComplement_zero_one [Fintype V]
    (A B : Finset V) :
    ({2, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement (({0, 1} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_two_three_eq_regionComplement_left,
    regionUnionPart_biUnion_zero_one]

/-- The left-only indexed region together with the outside region reconstructs
the complement of `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after the overlap is reinserted and injectivity of `B` is applied,
the remaining outside tensor is attached to the complement of `B`.
@isnad1 id=eq.0h3v.s6.b5d0cb5379a9 from=translated src=- shape=e1d1cb92 vocab=abeeaa22
-/
theorem regionUnionPart_zero_union_three_eq_regionComplement_right [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 3 = regionComplement B := by
  ext v
  simp only [regionUnionPart_zero, regionUnionPart_three, Finset.mem_union,
    mem_regionOnlyLeft, mem_regionOutsideUnion, mem_regionComplement]
  tauto

/-- The indexed subfamily `0,3` reconstructs the complement of `B`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap and applying injectivity of `B`, the
remaining diagram is carried by `A \ B` and the outside block.
@isnad1 id=eq.0h3v.s6.44d517da7b62 from=translated src=- shape=55880e38 vocab=dd546a9f
-/
theorem regionUnionPart_biUnion_zero_three_eq_regionComplement_right [Fintype V]
    (A B : Finset V) :
    ({0, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement B := by
  simpa [Finset.biUnion_insert, Finset.singleton_biUnion] using
    regionUnionPart_zero_union_three_eq_regionComplement_right A B

/-- The selected subfamily `0,3` is the complement of the selected subfamily
`1,2`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap and applying injectivity of \(B\),
the remaining indexed blocks are precisely the complement of the two blocks
forming \(B\).
@isnad1 id=eq.0h3v.s7.0d77af068c5e from=translated src=- shape=3e3af074 vocab=dd546a9f
-/
theorem regionUnionPart_biUnion_zero_three_eq_regionComplement_one_two [Fintype V]
    (A B : Finset V) :
    ({0, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B) =
      regionComplement (({1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_zero_three_eq_regionComplement_right,
    regionUnionPart_biUnion_one_two]

/-- The right-only and outside indexed regions form the complement of the
first two indexed regions.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after injectivity of \(A=(A\setminus B)\cup(A\cap B)\) is applied,
the remaining diagram is carried by the two complementary indexed pieces.
@isnad1 id=eq.0h3v.s6.023ddc76a27b from=translated src=- shape=4ed3f9b5 vocab=abeeaa22
-/
theorem regionUnionPart_two_union_three_eq_regionComplement_zero_union_one [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 2 ∪ regionUnionPart A B 3 =
      regionComplement (regionUnionPart A B 0 ∪ regionUnionPart A B 1) := by
  rw [regionUnionPart_two_union_three_eq_regionComplement_left,
    regionUnionPart_zero_union_one]

/-- The left-only and outside indexed regions form the complement of the middle
two indexed regions.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: after reinserting the overlap and applying injectivity of
\(B=(A\cap B)\cup(B\setminus A)\), the remaining diagram is carried by the
two complementary indexed pieces.
@isnad1 id=eq.0h3v.s6.bfd6001e2a79 from=translated src=- shape=4ed3f9b5 vocab=abeeaa22
-/
theorem regionUnionPart_zero_union_three_eq_regionComplement_one_union_two [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 3 =
      regionComplement (regionUnionPart A B 1 ∪ regionUnionPart A B 2) := by
  rw [regionUnionPart_zero_union_three_eq_regionComplement_right,
    regionUnionPart_one_union_two]

/-- The first two indexed regions are the complement of the right-only and
outside regions.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the first inversion step uses injectivity of the region
`A = (A \ B) ∪ (A ∩ B)`, whose complement is the remaining two indexed
pieces.
@isnad1 id=eq.0h3v.s6.013f05102566 from=translated src=- shape=4ed3f9b5 vocab=abeeaa22
-/
theorem regionUnionPart_zero_union_one_eq_regionComplement_two_union_three [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 0 ∪ regionUnionPart A B 1 =
      regionComplement (regionUnionPart A B 2 ∪ regionUnionPart A B 3) := by
  rw [regionUnionPart_zero_union_one, regionUnionPart_two_union_three_eq_regionComplement_left]
  ext v
  simp [regionComplement]

/-- The middle two indexed regions are the complement of the left-only and
outside regions.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the second inversion step uses injectivity of the region
`B = (A ∩ B) ∪ (B \ A)`, whose complement is the remaining two indexed
pieces.
@isnad1 id=eq.0h3v.s6.e7b7df5ee4db from=translated src=- shape=4ed3f9b5 vocab=abeeaa22
-/
theorem regionUnionPart_one_union_two_eq_regionComplement_zero_union_three [Fintype V]
    (A B : Finset V) :
    regionUnionPart A B 1 ∪ regionUnionPart A B 2 =
      regionComplement (regionUnionPart A B 0 ∪ regionUnionPart A B 3) := by
  rw [regionUnionPart_one_union_two, regionUnionPart_zero_union_three_eq_regionComplement_right]
  ext v
  simp [regionComplement]

/-- The indexed four regions cover the whole finite vertex set.
@isnad1 id=eq.0h3v.s5.cdbd1b16dcbd from=translated src=- shape=3d38f661 vocab=a2f31909
-/
theorem regionUnionPart_biUnion [Fintype V] (A B : Finset V) :
    Finset.univ.biUnion (regionUnionPart A B) = Finset.univ := by
  classical
  ext v
  constructor
  · intro _
    simp
  · intro _
    rcases regionFourPart_cases A B v with hv | hv | hv | hv
    · exact Finset.mem_biUnion.mpr ⟨0, by simp, by simpa using hv⟩
    · exact Finset.mem_biUnion.mpr ⟨1, by simp, by simpa using hv⟩
    · exact Finset.mem_biUnion.mpr ⟨2, by simp, by simpa using hv⟩
    · exact Finset.mem_biUnion.mpr ⟨3, by simp, by simpa using hv⟩

/-- Each vertex belongs to exactly one indexed part of the four-region
decomposition.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the proof blocks the tensor network into the four disjoint
regions `A \ B`, `A ∩ B`, `B \ A`, and `(A ∪ B)ᶜ`.
@isnad1 id=existsun.0h4v.s5.726c1a1e1b64 from=translated src=- shape=27ee92f8 vocab=7fd16694
-/
theorem regionUnionPart_exists_unique [Fintype V] (A B : Finset V) (v : V) :
    ∃! i : Fin 4, v ∈ regionUnionPart A B i := by
  by_cases hvA : v ∈ A
  · by_cases hvB : v ∈ B
    · refine ⟨1, by simp [hvA, hvB], ?_⟩
      intro j hj
      fin_cases j <;> simp [hvA, hvB] at hj ⊢
    · refine ⟨0, by simp [hvA, hvB], ?_⟩
      intro j hj
      fin_cases j <;> simp [hvA, hvB] at hj ⊢
  · by_cases hvB : v ∈ B
    · refine ⟨2, by simp [hvA, hvB], ?_⟩
      intro j hj
      fin_cases j <;> simp [hvA, hvB] at hj ⊢
    · refine ⟨3, by simp [hvA, hvB], ?_⟩
      intro j hj
      fin_cases j <;> simp [hvA, hvB] at hj ⊢

/-- The source union-closure assertion, applied to the selected indexed
subregions forming \(A\) and \(B\), makes the three inside indexed regions
injective.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404.  In the source proof, injectivity of
\((A\setminus B)\cup(A\cap B)\) and of
\((A\cap B)\cup(B\setminus A)\) gives injectivity of their union, namely the
three inside blocks \(A\setminus B\), \(A\cap B\), and \(B\setminus A\).
@isnad1 id=isinject.3h4v.s8.8669f6036180 from=translated src=- shape=b6ca873c vocab=7c349f37
-/
theorem RegionInjectivityUnionClosure.regionUnionPart_inside_injective [Fintype V]
    {κ : RegionInjectivityData V} (hUnion : RegionInjectivityUnionClosure κ)
    {A B : Finset V}
    (hA : κ.IsInjective (({0, 1} : Finset (Fin 4)).biUnion (regionUnionPart A B)))
    (hB : κ.IsInjective (({1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B))) :
    κ.IsInjective (({0, 1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_zero_one] at hA
  rw [regionUnionPart_biUnion_one_two] at hB
  rw [regionUnionPart_biUnion_zero_one_two]
  exact hUnion.union_injective hA hB

/-- Binary-union form of the four-region injectivity step.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404.  The source proof first uses injectivity of
\((A\setminus B)\cup(A\cap B)\), then reinserts the overlap and uses
injectivity of \((A\cap B)\cup(B\setminus A)\).  The remaining inside region
is \((A\setminus B)\cup(A\cap B)\cup(B\setminus A)=A\cup B\).
@isnad1 id=isinject.3h4v.s7.d4451b96ce8f from=translated src=- shape=df4f387f vocab=06ed7125
-/
theorem RegionInjectivityUnionClosure.regionUnionPart_inside_binary_injective [Fintype V]
    {κ : RegionInjectivityData V} (hUnion : RegionInjectivityUnionClosure κ)
    {A B : Finset V}
    (hA : κ.IsInjective (regionUnionPart A B 0 ∪ regionUnionPart A B 1))
    (hB : κ.IsInjective (regionUnionPart A B 1 ∪ regionUnionPart A B 2)) :
    κ.IsInjective
      (regionUnionPart A B 0 ∪ regionUnionPart A B 1 ∪ regionUnionPart A B 2) := by
  rw [regionUnionPart_zero_union_one] at hA
  rw [regionUnionPart_one_union_two] at hB
  rw [regionUnionPart_zero_union_one_union_two]
  exact hUnion.union_injective hA hB

/-- The left-only region is disjoint from the overlap.
@isnad1 id=disjoint.0h3v.s4.70c885a19dfa from=translated src=- shape=57616952 vocab=45244c74
-/
theorem regionOnlyLeft_disjoint_overlap (A B : Finset V) :
    Disjoint (regionOnlyLeft A B) (regionOverlap A B) := by
  simpa [regionOnlyLeft, regionOverlap] using Finset.disjoint_sdiff_inter A B

/-- The right-only region is disjoint from the overlap.
@isnad1 id=disjoint.0h3v.s4.b48d7fdcefa7 from=translated src=- shape=57616952 vocab=4b653124
-/
theorem regionOnlyRight_disjoint_overlap (A B : Finset V) :
    Disjoint (regionOnlyRight A B) (regionOverlap A B) := by
  simpa [regionOnlyRight, regionOverlap, Finset.inter_comm] using
    Finset.disjoint_sdiff_inter B A

/-- The left-only and right-only regions are disjoint.
@isnad1 id=disjoint.0h3v.s4.aaddfc7c2d21 from=translated src=- shape=57616952 vocab=8e58a923
-/
theorem regionOnlyLeft_disjoint_onlyRight (A B : Finset V) :
    Disjoint (regionOnlyLeft A B) (regionOnlyRight A B) := by
  simpa [regionOnlyLeft, regionOnlyRight] using
    (disjoint_sdiff_sdiff : Disjoint (A \ B) (B \ A))

/-- The left-only region is disjoint from the outside region.
@isnad1 id=disjoint.0h3v.s5.9af2df488d33 from=translated src=- shape=907f91ef vocab=88e47d26
-/
theorem regionOnlyLeft_disjoint_outside [Fintype V] (A B : Finset V) :
    Disjoint (regionOnlyLeft A B) (regionOutsideUnion A B) := by
  rw [Finset.disjoint_left]
  intro v hvLeft hvOutside
  exact (mem_regionOutsideUnion A B v).mp hvOutside |>.1 <|
    (mem_regionOnlyLeft A B v).mp hvLeft |>.1

/-- The overlap is disjoint from the outside region.
@isnad1 id=disjoint.0h3v.s5.b9e855f60091 from=translated src=- shape=907f91ef vocab=70b62bc0
-/
theorem regionOverlap_disjoint_outside [Fintype V] (A B : Finset V) :
    Disjoint (regionOverlap A B) (regionOutsideUnion A B) := by
  rw [Finset.disjoint_left]
  intro v hvOverlap hvOutside
  exact (mem_regionOutsideUnion A B v).mp hvOutside |>.1 <|
    (mem_regionOverlap A B v).mp hvOverlap |>.1

/-- The right-only region is disjoint from the outside region.
@isnad1 id=disjoint.0h3v.s5.1d5813eb4fff from=translated src=- shape=907f91ef vocab=a8acd795
-/
theorem regionOnlyRight_disjoint_outside [Fintype V] (A B : Finset V) :
    Disjoint (regionOnlyRight A B) (regionOutsideUnion A B) := by
  rw [Finset.disjoint_left]
  intro v hvRight hvOutside
  exact (mem_regionOutsideUnion A B v).mp hvOutside |>.2 <|
    (mem_regionOnlyRight A B v).mp hvRight |>.1

/-- The outside region is disjoint from the union of the three inside regions.
@isnad1 id=disjoint.0h3v.s5.9118a98f56fb from=translated src=- shape=bbdcf4c6 vocab=c59a671c
-/
theorem regionInside_disjoint_outside [Fintype V] (A B : Finset V) :
    Disjoint (regionOnlyLeft A B ∪ regionOverlap A B ∪ regionOnlyRight A B)
      (regionOutsideUnion A B) := by
  rw [regionThreePart_union]
  simpa [regionOutsideUnion] using
    (disjoint_sdiff_self_right :
      Disjoint (A ∪ B) ((Finset.univ : Finset V) \ (A ∪ B)))

/-- The indexed region \(A=(A\setminus B)\cup(A\cap B)\) is disjoint from the
two indexed pieces forming its complement.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: in the first inversion step, the tensor over \(A\) is removed and
the remaining diagram lives on the complementary indexed pieces.
@isnad1 id=disjoint.0h3v.s6.9401df96f6a4 from=translated src=- shape=ce224ebe vocab=de68b432
-/
theorem regionUnionPart_zero_one_disjoint_two_three [Fintype V] (A B : Finset V) :
    Disjoint (regionUnionPart A B 0 ∪ regionUnionPart A B 1)
      (regionUnionPart A B 2 ∪ regionUnionPart A B 3) := by
  rw [regionUnionPart_zero_union_one, regionUnionPart_two_union_three_eq_regionComplement_left]
  simpa [regionComplement] using
    (disjoint_sdiff_self_right : Disjoint A ((Finset.univ : Finset V) \ A))

/-- The indexed subfamily forming `A` is disjoint from the indexed subfamily
forming its complement.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the first inverse step separates the tensor over \(A\) from the
two complementary indexed blocks.
@isnad1 id=disjoint.0h3v.s7.15441aa5e714 from=translated src=- shape=75604bb1 vocab=2335314c
-/
theorem regionUnionPart_biUnion_zero_one_disjoint_two_three [Fintype V]
    (A B : Finset V) :
    Disjoint (({0, 1} : Finset (Fin 4)).biUnion (regionUnionPart A B))
      (({2, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_zero_one,
    regionUnionPart_biUnion_two_three_eq_regionComplement_left]
  simpa [regionComplement] using
    (disjoint_sdiff_self_right : Disjoint A ((Finset.univ : Finset V) \ A))

/-- The indexed region \(B=(A\cap B)\cup(B\setminus A)\) is disjoint from the
two indexed pieces forming its complement.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: in the second inversion step, the tensor over \(B\) is removed and
only the complementary indexed pieces remain.
@isnad1 id=disjoint.0h3v.s6.a11c681f3cc7 from=translated src=- shape=ce224ebe vocab=de68b432
-/
theorem regionUnionPart_one_two_disjoint_zero_three [Fintype V] (A B : Finset V) :
    Disjoint (regionUnionPart A B 1 ∪ regionUnionPart A B 2)
      (regionUnionPart A B 0 ∪ regionUnionPart A B 3) := by
  rw [regionUnionPart_one_union_two, regionUnionPart_zero_union_three_eq_regionComplement_right]
  simpa [regionComplement] using
    (disjoint_sdiff_self_right : Disjoint B ((Finset.univ : Finset V) \ B))

/-- The indexed subfamily forming `B` is disjoint from the indexed subfamily
forming its complement.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the second inverse step separates the tensor over \(B\) from the
two complementary indexed blocks.
@isnad1 id=disjoint.0h3v.s7.f07a9eee76ab from=translated src=- shape=75604bb1 vocab=2335314c
-/
theorem regionUnionPart_biUnion_one_two_disjoint_zero_three [Fintype V]
    (A B : Finset V) :
    Disjoint (({1, 2} : Finset (Fin 4)).biUnion (regionUnionPart A B))
      (({0, 3} : Finset (Fin 4)).biUnion (regionUnionPart A B)) := by
  rw [regionUnionPart_biUnion_one_two,
    regionUnionPart_biUnion_zero_three_eq_regionComplement_right]
  simpa [regionComplement] using
    (disjoint_sdiff_self_right : Disjoint B ((Finset.univ : Finset V) \ B))

/-- The union of the three inside indexed regions is disjoint from the outside
indexed region.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404: the tensor called `X` in the proof is attached to the outside
block, separated from the three blocks inside `A ∪ B`.
@isnad1 id=disjoint.0h3v.s6.59184e3d63dc from=translated src=- shape=5e737f87 vocab=de68b432
-/
theorem regionUnionPart_inside_disjoint_three [Fintype V] (A B : Finset V) :
    Disjoint (regionUnionPart A B 0 ∪ regionUnionPart A B 1 ∪ regionUnionPart A B 2)
      (regionUnionPart A B 3) := by
  simpa using regionInside_disjoint_outside A B

/-- The indexed four regions are pairwise disjoint.
@isnad1 id=pairwise.0h3v.s5.408047c078e8 from=translated src=- shape=a2ba226c vocab=15324189
-/
theorem regionUnionPart_pairwise_disjoint [Fintype V] (A B : Finset V) :
    Pairwise fun i j : Fin 4 =>
      Disjoint (regionUnionPart A B i) (regionUnionPart A B j) := by
  classical
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa using regionOnlyLeft_disjoint_overlap A B
  · simpa using regionOnlyLeft_disjoint_onlyRight A B
  · simpa using regionOnlyLeft_disjoint_outside A B
  · simpa using (regionOnlyLeft_disjoint_overlap A B).symm
  · exact (hij rfl).elim
  · simpa using (regionOnlyRight_disjoint_overlap A B).symm
  · simpa using regionOverlap_disjoint_outside A B
  · simpa using (regionOnlyLeft_disjoint_onlyRight A B).symm
  · simpa using regionOnlyRight_disjoint_overlap A B
  · exact (hij rfl).elim
  · simpa using regionOnlyRight_disjoint_outside A B
  · simpa using (regionOnlyLeft_disjoint_outside A B).symm
  · simpa using (regionOverlap_disjoint_outside A B).symm
  · simpa using (regionOnlyRight_disjoint_outside A B).symm
  · exact (hij rfl).elim

end PEPS
end TNLean
