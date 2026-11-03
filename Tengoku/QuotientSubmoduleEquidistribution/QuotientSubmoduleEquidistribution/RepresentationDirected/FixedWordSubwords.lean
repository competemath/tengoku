import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordInterface
import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Data.Fin.Rev
import Tengoku.Seed.Data.Set.Finite.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reduced subwords of a fixed Coxeter word

This file develops the finite-candidate, lexicographic-minimum, and
word-reversal API needed by the representation-directed argument.  It does
not assume that the ambient word is reduced and does not depend on a global
Bruhat-order development.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordSubwords

open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWord

universe uB uW

variable {B : Type uB} {W : Type uW}
variable [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

/-- Group elements admitting a reduced expression selected from `ambient`.-/
def FixedWordElement (ambient : List B) :=
  {w : W // ∃ positions : Finset (Fin ambient.length),
    IsReducedSubwordFor cs ambient w positions}

/--
@isnad1 id=finite.0h5v.s5.62e060fc1ca6 from=translated src=- shape=a7cd64c2 vocab=d8543f00
-/
theorem fixedWordElement_set_finite (ambient : List B) :
    {w : W | ∃ positions : Finset (Fin ambient.length),
      IsReducedSubwordFor cs ambient w positions}.Finite := by
  let productAt : Finset (Fin ambient.length) → W :=
    fun positions => cs.wordProd (subwordAt ambient positions)
  apply (Set.finite_range productAt).subset
  intro w hw
  obtain ⟨positions, _hreduced, hprod⟩ := hw
  exact ⟨positions, hprod⟩

noncomputable instance fixedWordElementFintype (ambient : List B) :
    Fintype (FixedWordElement cs ambient) :=
  (fixedWordElement_set_finite cs ambient).fintype

/-- All reduced position witnesses for `w` inside `ambient`.-/
def reducedPositionCandidates
    (ambient : List B) (w : W) :
    Finset (Finset (Fin ambient.length)) := by
  classical
  exact Finset.univ.filter (IsReducedSubwordFor cs ambient w)

/--
@isnad1 id=iff.0h7v.s6.d9662f95aa36 from=translated src=- shape=7924175c vocab=be9fbb5e
-/
@[simp]
theorem mem_reducedPositionCandidates_iff
    (ambient : List B) (w : W)
    (positions : Finset (Fin ambient.length)) :
    positions ∈ reducedPositionCandidates cs ambient w ↔
      IsReducedSubwordFor cs ambient w positions := by
  simp [reducedPositionCandidates]

/--
@isnad1 id=nonempty.0h6v.s6.74b97393cde0 from=translated src=- shape=e93beeb9 vocab=ea14bfeb
-/
theorem reducedPositionCandidates_nonempty
    (ambient : List B) (w : FixedWordElement cs ambient) :
    (reducedPositionCandidates cs ambient w.1).Nonempty := by
  obtain ⟨positions, hpositions⟩ := w.property
  exact ⟨positions,
    (mem_reducedPositionCandidates_iff cs ambient w.1 positions).2 hpositions⟩

/-- Every element represented by a reduced subword has a lexicographically
leftmost reduced position witness.
@isnad1 id=ex.0h6v.s6.4b5033c94444 from=translated src=- shape=98fd8505 vocab=b79e4746
-/
theorem exists_leftmostReducedSubwordFor
    (ambient : List B) (w : FixedWordElement cs ambient) :
    ∃ positions : Finset (Fin ambient.length),
      IsLeftmostReducedSubwordFor cs ambient w.1 positions := by
  classical
  obtain ⟨positions, hpositions, hminimal⟩ :=
    Finset.exists_min_image
      (reducedPositionCandidates cs ambient w.1)
      (fun positions => positions.sort (· ≤ ·))
      (reducedPositionCandidates_nonempty cs ambient w)
  refine ⟨positions,
    (mem_reducedPositionCandidates_iff cs ambient w.1 positions).1 hpositions,
    ?_⟩
  intro other hother hlex
  have hle := hminimal other
    ((mem_reducedPositionCandidates_iff cs ambient w.1 other).2 hother)
  have hlt : other.sort (· ≤ ·) < positions.sort (· ≤ ·) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  exact (not_lt_of_ge hle) hlt

/-- A chosen lexicographically first reduced position set.-/
def lexFirstPositions
    (ambient : List B) (w : FixedWordElement cs ambient) :
    Finset (Fin ambient.length) :=
  (exists_leftmostReducedSubwordFor cs ambient w).choose

/--
@isnad1 id=isleftmo.0h6v.s6.9783b7b5f303 from=translated src=- shape=2c487016 vocab=528e9a84
-/
theorem lexFirstPositions_spec
    (ambient : List B) (w : FixedWordElement cs ambient) :
    IsLeftmostReducedSubwordFor cs ambient w.1
      (lexFirstPositions cs ambient w) :=
  (exists_leftmostReducedSubwordFor cs ambient w).choose_spec

/-! ## Reversal with a fixed index length -/

/-- Reverse a set of positions in `Fin n`.-/
def reversePositions {n : ℕ} (positions : Finset (Fin n)) :
    Finset (Fin n) :=
  positions.map Fin.revPerm.toEmbedding

/--
@isnad1 id=iff.0h3v.s5.36df4e65b595 from=translated src=- shape=1a7aa6a3 vocab=8942853b
-/
@[simp]
theorem mem_reversePositions_iff {n : ℕ}
    (positions : Finset (Fin n)) (i : Fin n) :
    i ∈ reversePositions positions ↔ i.rev ∈ positions := by
  simp [reversePositions]

/--
@isnad1 id=eq.0h2v.s4.7366e64c1650 from=translated src=- shape=e99e161d vocab=ffd0332e
-/
@[simp]
theorem card_reversePositions {n : ℕ}
    (positions : Finset (Fin n)) :
    (reversePositions positions).card = positions.card := by
  simp [reversePositions]

/--
@isnad1 id=eq.0h2v.s4.36ead3617d59 from=translated src=- shape=60f8d03b vocab=0c247154
-/
@[simp]
theorem reversePositions_reversePositions {n : ℕ}
    (positions : Finset (Fin n)) :
    reversePositions (reversePositions positions) = positions := by
  ext i
  simp

/-- Select positions from an `n`-indexed word.  This cast-free variant is the
convenient core for proving reversal identities.-/
def subwordAtFn {n : ℕ}
    (word : Fin n → B) (positions : Finset (Fin n)) : List B :=
  (positions.sort (· ≤ ·)).map word

/-- Reversing both an indexed word and its selected positions reverses the
selected subword.
@isnad1 id=eq.0h4v.s5.d807e380d947 from=translated src=- shape=809e160d vocab=70505d3c
-/
theorem subwordAtFn_reverse {n : ℕ}
    (word : Fin n → B) (positions : Finset (Fin n)) :
    subwordAtFn (word ∘ Fin.rev) (reversePositions positions) =
      (subwordAtFn word positions).reverse := by
  have hdescending :
      ((positions.sort (· ≤ ·)).map Fin.rev).SortedGT := by
    rw [List.sortedGT_iff_pairwise, List.pairwise_map]
    exact positions.sortedLT_sort.pairwise.imp
      fun hij => Fin.rev_lt_rev.mpr hij
  have hmembership :
      ∀ i : Fin n,
        i ∈ (positions.sort (· ≤ ·)).map Fin.rev ↔
          i ∈ (reversePositions positions).sort (· ≤ ·) := by
    intro i
    simp only [List.mem_map, Finset.mem_sort,
      mem_reversePositions_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hi
      exact ⟨i.rev, hi, Fin.rev_rev i⟩
  have hmapped :
      (positions.sort (· ≤ ·)).map Fin.rev =
        ((reversePositions positions).sort (· ≤ ·)).reverse :=
    hdescending.eq_reverse_of_mem_iff_of_sortedLT
      hmembership (reversePositions positions).sortedLT_sort
  have hsorted :
      (reversePositions positions).sort (· ≤ ·) =
        ((positions.sort (· ≤ ·)).map Fin.rev).reverse := by
    simpa using congrArg List.reverse hmapped.symm
  simp [subwordAtFn, hsorted, List.map_reverse, Function.comp_def]

/--
@isnad1 id=eq.0h3v.s4.fb58bb36253a from=translated src=- shape=b5a11cde vocab=2e2feacd
-/
@[simp]
theorem subwordAtFn_get
    (word : List B) (positions : Finset (Fin word.length)) :
    subwordAtFn word.get positions = subwordAt word positions :=
  rfl

/-! ## Reversal for the repository's list-indexed `subwordAt` -/

/-- The order-reversing equivalence from positions of `word` to positions of
`word.reverse`.  The final cast only transports across `length_reverse`.-/
def reverseIndexEquiv (word : List B) :
    Fin word.length ≃ Fin word.reverse.length :=
  Fin.revPerm.trans
    (Fin.castOrderIso (by simp)).toEquiv

/--
@isnad1 id=eq.0h3v.s6.6838cd352851 from=translated src=- shape=cd6632dc vocab=798346b1
-/
@[simp]
theorem reverseIndexEquiv_apply_val
    (word : List B) (i : Fin word.length) :
    (reverseIndexEquiv word i).val = i.rev.val := by
  rfl

/--
@isnad1 id=strictan.0h2v.s6.e337ff7672e2 from=translated src=- shape=096d6387 vocab=ce20b73e
-/
theorem reverseIndexEquiv_strictAnti
    (word : List B) :
    StrictAnti (reverseIndexEquiv word) := by
  intro i j hij
  simpa [reverseIndexEquiv] using Fin.rev_lt_rev.mpr hij

/--
@isnad1 id=eq.0h3v.s6.982ddaf12fb4 from=translated src=- shape=c9ca7f32 vocab=ba27e2f6
-/
@[simp]
theorem get_reverse_reverseIndexEquiv
    (word : List B) (i : Fin word.length) :
    word.reverse.get (reverseIndexEquiv word i) = word.get i := by
  change word.reverse[(reverseIndexEquiv word i).val] = word[i.val]
  rw [List.getElem_reverse]
  congr
  simp [reverseIndexEquiv, Fin.rev]
  omega

/-- Reverse selected positions while changing from `word` to `word.reverse`.-/
def reversePositionsIn
    (word : List B) (positions : Finset (Fin word.length)) :
    Finset (Fin word.reverse.length) :=
  positions.map (reverseIndexEquiv word).toEmbedding

/--
@isnad1 id=eq.0h3v.s4.a3117f58b310 from=translated src=- shape=c5f45c47 vocab=5ccf2a31
-/
@[simp]
theorem card_reversePositionsIn
    (word : List B) (positions : Finset (Fin word.length)) :
    (reversePositionsIn word positions).card = positions.card := by
  simp [reversePositionsIn]

/-- Literal list form: selecting the reversed positions from the reversed
ambient word gives the reverse selected subword.
@isnad1 id=eq.0h3v.s4.1b05ced7f50b from=translated src=- shape=6f7b74b7 vocab=d47cbb32
-/
theorem subwordAt_reverse
    (word : List B) (positions : Finset (Fin word.length)) :
    subwordAt word.reverse (reversePositionsIn word positions) =
      (subwordAt word positions).reverse := by
  have hdescending :
      ((positions.sort (· ≤ ·)).map
        (reverseIndexEquiv word)).SortedGT := by
    rw [List.sortedGT_iff_pairwise, List.pairwise_map]
    exact positions.sortedLT_sort.pairwise.imp
      fun hij => reverseIndexEquiv_strictAnti word hij
  have hmembership :
      ∀ i : Fin word.reverse.length,
        i ∈ (positions.sort (· ≤ ·)).map
            (reverseIndexEquiv word) ↔
          i ∈ (reversePositionsIn word positions).sort (· ≤ ·) := by
    intro i
    simp only [List.mem_map, Finset.mem_sort,
      reversePositionsIn, Finset.mem_map, Equiv.coe_toEmbedding]
  have hmapped :
      (positions.sort (· ≤ ·)).map (reverseIndexEquiv word) =
        ((reversePositionsIn word positions).sort (· ≤ ·)).reverse :=
    hdescending.eq_reverse_of_mem_iff_of_sortedLT
      hmembership (reversePositionsIn word positions).sortedLT_sort
  have hsorted :
      (reversePositionsIn word positions).sort (· ≤ ·) =
        ((positions.sort (· ≤ ·)).map
          (reverseIndexEquiv word)).reverse := by
    simpa using congrArg List.reverse hmapped.symm
  have hget :
      word.reverse.get ∘ reverseIndexEquiv word = word.get := by
    funext i
    exact get_reverse_reverseIndexEquiv word i
  simp only [subwordAt, hsorted, List.map_reverse, List.map_map]
  rw [hget]

/-- Reversal transports a reduced subword witness for `w` to one for
`w⁻¹` in the reversed ambient word.
@isnad1 id=iff.0h7v.s5.6e5910ada06d from=translated src=- shape=9d520b26 vocab=a6c5ea06
-/
@[simp]
theorem isReducedSubwordFor_reverse_iff
    (word : List B) (w : W)
    (positions : Finset (Fin word.length)) :
    IsReducedSubwordFor cs word.reverse w⁻¹
        (reversePositionsIn word positions) ↔
      IsReducedSubwordFor cs word w positions := by
  simp [IsReducedSubwordFor, subwordAt_reverse]

end QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordSubwords
