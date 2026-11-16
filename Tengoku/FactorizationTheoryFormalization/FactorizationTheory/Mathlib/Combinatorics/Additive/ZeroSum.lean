/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Tengoku.Seed.Algebra.BigOperators.Group.Multiset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Zero-sum sequences

A sequence over an additive commutative monoid `G` is represented by a multiset of elements of
`G`. This file develops zero-sum sequences and their behavior under additive maps.

## Main declarations

* `Multiset.IsZeroSum`: the terms of a sequence sum to zero.
* `Multiset.IsZeroSumFree`: no nonempty subsequence sums to zero.
* `Multiset.IsMinimalZeroSum`: a nonempty zero-sum sequence with no proper nonempty zero-sum
  subsequence.

The predicates and their order-theoretic API require only an additive commutative monoid.
Constructions involving the negated sum of a sequence require an additive commutative group.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]

## Tags

additive combinatorics, zero-sum sequence
-/

public section

assert_not_exists Field Ideal

variable {G : Type*} {S T : Multiset G} {g : G}

namespace Multiset

/-! ### Zero-sum sequences -/

section AddCommMonoid

variable [AddCommMonoid G]

/-- A sequence over an additive commutative monoid is *zero-sum* if its terms sum to `0`. The
empty sequence is zero-sum.-/
def IsZeroSum (S : Multiset G) : Prop :=
  S.sum = 0

/--
@isnad1 id=iff.0h2v.s5.08c807418fff from=translated src=- shape=100bd963 vocab=c6fddc17
-/
theorem isZeroSum_iff : IsZeroSum S ↔ S.sum = 0 := by
  rfl

/--
@isnad1 id=iszerosu.0h1v.s4.98cd8a978bde from=translated src=- shape=a72970d9 vocab=f7f9867c
-/
@[simp]
theorem isZeroSum_zero : IsZeroSum (0 : Multiset G) :=
  Multiset.sum_zero

/--
@isnad1 id=iff.0h2v.s5.acd594cf6315 from=translated src=- shape=680ecb7a vocab=76bbaf1a
-/
@[simp]
theorem isZeroSum_singleton : IsZeroSum ({g} : Multiset G) ↔ g = 0 := by
  rw [isZeroSum_iff, Multiset.sum_singleton]

/--
@isnad1 id=iszerosu.2h3v.s5.44633a3267d9 from=translated src=- shape=270d490a vocab=ff3f69b1
-/
theorem IsZeroSum.add (hS : IsZeroSum S) (hT : IsZeroSum T) : IsZeroSum (S + T) := by
  rw [isZeroSum_iff, Multiset.sum_add, hS, hT, add_zero]

/-- An additive monoid homomorphism carries zero-sum sequences to zero-sum sequences.
@isnad1 id=iszerosu.1h5v.s5.3975dc533269 from=translated src=- shape=72baf42e vocab=98e47968
-/
lemma IsZeroSum.map {H F : Type*} [AddCommMonoid H] [FunLike F G H]
    [AddMonoidHomClass F G H] (hS : IsZeroSum S) (f : F) :
    IsZeroSum (S.map f) := by
  rw [isZeroSum_iff, ← map_multiset_sum, hS, _root_.map_zero]

/--
@isnad1 id=iff.1h5v.s6.1e8203479804 from=translated src=- shape=a97d1c21 vocab=9ec49fc5
-/
lemma isZeroSum_map_iff_of_injective {H F : Type*} [AddCommMonoid H] [FunLike F G H]
    [AddMonoidHomClass F G H] (f : F) (hf : Function.Injective f) :
    IsZeroSum (S.map f) ↔ IsZeroSum S := by
  rw [isZeroSum_iff, isZeroSum_iff, ← map_multiset_sum, ← _root_.map_zero f, hf.eq_iff]

/--
@isnad1 id=iff.0h4v.s6.dc5ede774f25 from=translated src=- shape=5f4dc7e8 vocab=4cac05d0
-/
@[simp]
theorem isZeroSum_map_addEquiv_iff {H : Type*} [AddCommMonoid H] (e : G ≃+ H) :
    IsZeroSum (S.map e) ↔ IsZeroSum S :=
  isZeroSum_map_iff_of_injective e.toAddMonoidHom e.injective

/-- If a concatenation is zero-sum and its left part is zero-sum, then its right part is
zero-sum.
@isnad1 id=iszerosu.2h3v.s5.569fed43e983 from=translated src=- shape=d96078c7 vocab=ff3f69b1
-/
theorem IsZeroSum.of_add_left (hST : IsZeroSum (S + T)) (hS : IsZeroSum S) : IsZeroSum T := by
  rw [isZeroSum_iff, Multiset.sum_add, hS, zero_add] at hST
  exact hST

/--
@isnad1 id=iszerosu.2h3v.s5.1e741f54f472 from=translated src=- shape=ee27f703 vocab=ff3f69b1
-/
theorem IsZeroSum.of_add_right (hST : IsZeroSum (S + T)) (hT : IsZeroSum T) : IsZeroSum S :=
  IsZeroSum.of_add_left (S := T) (by rwa [add_comm]) hT

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G]

/--
@isnad1 id=iszerosu.0h2v.s5.1b19249aa1bd from=translated src=- shape=13966a44 vocab=eec11a13
-/
theorem isZeroSum_cons_neg_sum (S : Multiset G) : IsZeroSum (-S.sum ::ₘ S) := by
  rw [isZeroSum_iff, Multiset.sum_cons, neg_add_cancel]

end AddCommGroup

/-! ### Zero-sum free sequences -/

section AddCommMonoid

variable [AddCommMonoid G]

/-- A sequence is *zero-sum free* if none of its nonempty subsequences is zero-sum. The empty
sequence is zero-sum free.-/
def IsZeroSumFree (S : Multiset G) : Prop :=
  ∀ ⦃T : Multiset G⦄, T ≤ S → T ≠ 0 → ¬IsZeroSum T

/--
@isnad1 id=iff.0h2v.s5.ace5c825c998 from=translated src=- shape=e8fb5e42 vocab=15a01a04
-/
theorem isZeroSumFree_iff :
    IsZeroSumFree S ↔ ∀ ⦃T : Multiset G⦄, T ≤ S → T ≠ 0 → ¬IsZeroSum T := by
  rfl

/--
@isnad1 id=iff.0h2v.s5.c92ef359cf7a from=translated src=- shape=eb219635 vocab=15a01a04
-/
@[simp]
lemma not_isZeroSumFree :
    ¬IsZeroSumFree S ↔ ∃ T ≤ S, T ≠ 0 ∧ IsZeroSum T := by
  simp [IsZeroSumFree]

/--
@isnad1 id=iszerosu.0h1v.s4.432fc5d56a66 from=translated src=- shape=a72970d9 vocab=5343e544
-/
@[simp]
theorem isZeroSumFree_zero : IsZeroSumFree (0 : Multiset G) := by
  intro T hT hT0
  exact (hT0 (Multiset.le_zero.mp hT)).elim

/--
@isnad1 id=iff.0h2v.s5.aa7dda555200 from=translated src=- shape=680ecb7a vocab=51d6eaf6
-/
@[simp]
lemma isZeroSumFree_singleton : IsZeroSumFree ({g} : Multiset G) ↔ g ≠ 0 := by
  simp [IsZeroSumFree, IsZeroSum]

/--
@isnad1 id=iszerosu.2h3v.s5.db27ce724e5f from=translated src=- shape=ffc52af3 vocab=9c8a5694
-/
theorem IsZeroSumFree.mono (hS : IsZeroSumFree S) (hTS : T ≤ S) : IsZeroSumFree T :=
  fun _ hUT hU ↦ hS (hUT.trans hTS) hU

/--
@isnad1 id=not.1h2v.s5.e10ba2232c25 from=translated src=- shape=96ffa274 vocab=67738013
-/
theorem IsZeroSumFree.notMem_zero (hS : IsZeroSumFree S) : (0 : G) ∉ S := fun h ↦
  hS (Multiset.singleton_le.mpr h) (Multiset.singleton_ne_zero _) (isZeroSum_singleton.mpr rfl)

/--
@isnad1 id=not.2h2v.s5.040acd913cc5 from=translated src=- shape=51cef38e vocab=c0d21930
-/
lemma IsZeroSumFree.not_isZeroSum_of_ne_zero (hS : IsZeroSumFree S) (hne : S ≠ 0) :
    ¬IsZeroSum S :=
  hS le_rfl hne

private theorem exists_le_map_eq_of_le_map {α β : Type*} [Nonempty α] {f : α → β}
    (hf : Function.Injective f) {s : Multiset α} {t : Multiset β} (h : t ≤ s.map f) :
    ∃ u ≤ s, u.map f = t := by
  let u := t.map (Function.invFun f)
  have hu : u.map f = t := by
    change (t.map (Function.invFun f)).map f = t
    rw [Multiset.map_map]
    calc
      t.map (f ∘ Function.invFun f) = t.map id := by
        apply Multiset.map_congr rfl
        intro x hx
        obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le h hx)
        exact congrArg f (Function.leftInverse_invFun hf y)
      _ = t := Multiset.map_id t
  refine ⟨u, ?_, hu⟩
  apply (Multiset.map_le_map_iff hf).mp
  rw [hu]
  exact h

/--
@isnad1 id=iff.1h5v.s6.726adaa77969 from=translated src=- shape=a97d1c21 vocab=3ee7e420
-/
lemma isZeroSumFree_map_iff_of_injective {H F : Type*} [AddCommMonoid H] [FunLike F G H]
    [AddMonoidHomClass F G H] (f : F) (hf : Function.Injective f) :
    IsZeroSumFree (S.map f) ↔ IsZeroSumFree S := by
  constructor
  · intro hS T hTS hT hTsum
    exact hS (Multiset.map_le_map hTS) (by simpa using hT) (hTsum.map f)
  · intro hS T hTS hT hTsum
    obtain ⟨U, hUS, rfl⟩ := exists_le_map_eq_of_le_map hf hTS
    exact hS hUS (by simpa using hT) ((isZeroSum_map_iff_of_injective f hf).mp hTsum)

/--
@isnad1 id=iszerosu.2h5v.s6.c43f3139defe from=translated src=- shape=636ca936 vocab=3ee7e420
-/
alias ⟨_, IsZeroSumFree.map⟩ := isZeroSumFree_map_iff_of_injective

/--
@isnad1 id=iff.0h4v.s6.12168f9cbc92 from=translated src=- shape=5f4dc7e8 vocab=d508279f
-/
@[simp]
theorem isZeroSumFree_map_addEquiv_iff {H : Type*} [AddCommMonoid H] (e : G ≃+ H) :
    IsZeroSumFree (S.map e) ↔ IsZeroSumFree S :=
  isZeroSumFree_map_iff_of_injective e.toAddMonoidHom e.injective

/-! ### Minimal zero-sum sequences -/

/-- A sequence is *minimal zero-sum* if it is nonempty, is zero-sum, and none of its proper
nonempty subsequences is zero-sum.-/
def IsMinimalZeroSum (S : Multiset G) : Prop :=
  IsZeroSum S ∧ S ≠ 0 ∧
    ∀ ⦃T : Multiset G⦄, T ≤ S → T ≠ 0 → T ≠ S → ¬IsZeroSum T

/--
@isnad1 id=iff.0h2v.s6.296f093c0211 from=translated src=- shape=8092477b vocab=72f7677f
-/
theorem isMinimalZeroSum_iff :
    IsMinimalZeroSum S ↔ IsZeroSum S ∧ S ≠ 0 ∧
      ∀ ⦃T : Multiset G⦄, T ≤ S → T ≠ 0 → T ≠ S → ¬IsZeroSum T := by
  rfl

/--
@isnad1 id=iszerosu.1h2v.s4.7cefa46615f3 from=translated src=- shape=ce7c1191 vocab=b73b533c
-/
theorem IsMinimalZeroSum.isZeroSum (hS : IsMinimalZeroSum S) : IsZeroSum S :=
  hS.1

/--
@isnad1 id=ne.1h2v.s4.73723abe6307 from=translated src=- shape=ee7f8dc1 vocab=d2495192
-/
theorem IsMinimalZeroSum.ne_zero (hS : IsMinimalZeroSum S) : S ≠ 0 :=
  hS.2.1

/--
@isnad1 id=not.4h3v.s5.6b940342a75c from=translated src=- shape=ec59aaba vocab=72f7677f
-/
theorem IsMinimalZeroSum.not_isZeroSum (hS : IsMinimalZeroSum S) (hTS : T ≤ S) (hT : T ≠ 0)
    (hne : T ≠ S) : ¬IsZeroSum T :=
  hS.2.2 hTS hT hne

/--
@isnad1 id=lt.1h2v.s4.557cc1d22852 from=translated src=- shape=d1fb41dc vocab=0539f123
-/
theorem IsMinimalZeroSum.card_pos (hS : IsMinimalZeroSum S) : 0 < S.card :=
  Multiset.card_pos.mpr hS.ne_zero

/--
@isnad1 id=ne.1h2v.s4.296ab013553a from=translated src=- shape=10fd51ff vocab=63cf70a9
-/
theorem IsMinimalZeroSum.card_ne_zero (hS : IsMinimalZeroSum S) : S.card ≠ 0 :=
  hS.card_pos.ne'

/--
@isnad1 id=iff.1h5v.s6.51ba0d5bbbf6 from=translated src=- shape=a97d1c21 vocab=c41cf1d5
-/
lemma isMinimalZeroSum_map_iff_of_injective {H F : Type*} [AddCommMonoid H] [FunLike F G H]
    [AddMonoidHomClass F G H] (f : F) (hf : Function.Injective f) :
    IsMinimalZeroSum (S.map f) ↔ IsMinimalZeroSum S := by
  constructor
  · intro hS
    refine ⟨(isZeroSum_map_iff_of_injective f hf).mp hS.isZeroSum, ?_, ?_⟩
    · simpa using hS.ne_zero
    · intro T hTS hT hTne hTsum
      apply hS.not_isZeroSum (Multiset.map_le_map hTS) (by simpa using hT)
      · exact fun h ↦ hTne (Multiset.map_injective hf h)
      · exact hTsum.map f
  · intro hS
    refine ⟨hS.isZeroSum.map f, by simpa using hS.ne_zero, ?_⟩
    intro T hTS hT hTne hTsum
    obtain ⟨U, hUS, rfl⟩ := exists_le_map_eq_of_le_map hf hTS
    apply hS.not_isZeroSum hUS (by simpa using hT)
    · exact fun h ↦ hTne (congrArg (Multiset.map f) h)
    · exact (isZeroSum_map_iff_of_injective f hf).mp hTsum

/--
@isnad1 id=isminima.2h5v.s6.a638e85f4043 from=translated src=- shape=636ca936 vocab=c41cf1d5
-/
alias ⟨_, IsMinimalZeroSum.map⟩ := isMinimalZeroSum_map_iff_of_injective

/--
@isnad1 id=iff.0h4v.s6.84147da00be1 from=translated src=- shape=5f4dc7e8 vocab=408fb3a2
-/
@[simp]
theorem isMinimalZeroSum_map_addEquiv_iff {H : Type*} [AddCommMonoid H] (e : G ≃+ H) :
    IsMinimalZeroSum (S.map e) ↔ IsMinimalZeroSum S :=
  isMinimalZeroSum_map_iff_of_injective e.toAddMonoidHom e.injective

/-- An additive equivalence carries minimal zero-sum sequences to minimal zero-sum sequences.
@isnad1 id=isminima.1h4v.s6.c75af0e9b1bd from=translated src=- shape=b87cb7fb vocab=408fb3a2
-/
theorem IsMinimalZeroSum.map_addEquiv {H : Type*} [AddCommMonoid H]
    (hS : IsMinimalZeroSum S) (e : G ≃+ H) : IsMinimalZeroSum (S.map e) :=
  hS.map e.toAddMonoidHom e.injective

/--
@isnad1 id=iff.0h2v.s5.38fee9acd541 from=translated src=- shape=680ecb7a vocab=84e70f59
-/
@[simp]
theorem isMinimalZeroSum_singleton : IsMinimalZeroSum ({g} : Multiset G) ↔ g = 0 := by
  refine ⟨fun hS ↦ isZeroSum_singleton.mp hS.isZeroSum, ?_⟩
  rintro rfl
  refine ⟨isZeroSum_singleton.mpr rfl, Multiset.singleton_ne_zero _, fun T hTS hT hne ↦ ?_⟩
  exact absurd ((Multiset.le_singleton.mp hTS).resolve_left hT) hne

/-- A minimal zero-sum sequence containing `0` is the singleton `{0}`: otherwise `{0}` would be a
proper nonempty zero-sum subsequence.-/
theorem IsMinimalZeroSum.eq_singleton_of_zero_mem (hS : IsMinimalZeroSum S) (h : (0 : G) ∈ S) :
    S = {0} := by
  by_contra hne
  exact hS.not_isZeroSum (Multiset.singleton_le.mpr h) (Multiset.singleton_ne_zero _)
    (Ne.symm hne) (isZeroSum_singleton.mpr rfl)

/-- Deleting one term of a minimal zero-sum sequence leaves a zero-sum free sequence.
@isnad1 id=iszerosu.1h3v.s4.6cf692e87540 from=translated src=- shape=920e719c vocab=735d8116
-/
theorem IsMinimalZeroSum.isZeroSumFree_of_cons (hS : IsMinimalZeroSum (g ::ₘ S)) :
    IsZeroSumFree S := by
  intro T hTS hT hTsum
  apply hS.not_isZeroSum (hTS.trans (Multiset.le_cons_self S g)) hT ?_ hTsum
  rintro rfl
  have hcard := Multiset.card_le_card hTS
  exact (Nat.not_succ_le_self S.card) (by simpa only [Multiset.card_cons] using hcard)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G]

/-- Appending the negated sum to a zero-sum free sequence produces a minimal zero-sum sequence.
@isnad1 id=isminima.1h2v.s5.78e9f748bffc from=translated src=- shape=4a4f0dbd vocab=301e6bc9
-/
theorem IsZeroSumFree.isMinimalZeroSum_cons_neg_sum (hS : IsZeroSumFree S) :
    IsMinimalZeroSum (-S.sum ::ₘ S) := by
  refine ⟨isZeroSum_cons_neg_sum S, Multiset.cons_ne_zero, ?_⟩
  intro T hT hT0 hTne hTsum
  classical
  -- If the new term occurs, its complement in the sequence contradicts zero-sum freeness;
  -- otherwise the subsequence itself does.
  by_cases hneg : -S.sum ∈ T
  · obtain ⟨T', rfl⟩ := Multiset.exists_cons_of_mem hneg
    obtain ⟨U, hU⟩ := Multiset.le_iff_exists_add.mp hT
    have hU0 : U ≠ 0 := by
      rintro rfl
      simp at hU
      exact hTne (congrArg (fun V ↦ -S.sum ::ₘ V) hU.symm)
    have hTU : T' + U = S := by
      simpa [Multiset.cons_add] using hU.symm
    apply hS (Multiset.le_add_left U T' |>.trans hTU.le) hU0
    apply IsZeroSum.of_add_left (S := -S.sum ::ₘ T')
    · rw [← hU]
      exact isZeroSum_cons_neg_sum S
    · exact hTsum
  · exact hS ((Multiset.le_cons_of_notMem hneg).mp hT) hT0 hTsum

end AddCommGroup

end Multiset
