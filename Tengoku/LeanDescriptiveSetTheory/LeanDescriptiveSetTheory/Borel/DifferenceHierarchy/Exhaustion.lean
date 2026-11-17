/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.DifferenceHierarchy.Closure
import Tengoku.Seed.Topology.Baire.CompleteMetrizable
import Tengoku.Seed.Topology.MetricSpace.Polish

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hausdorff derivatives and the exhaustion proof

This file develops the transfinite closed derivative used in the Hausdorff--Kuratowski theorem.
The derivative of `s` starts at the whole space, intersects the closures of the two relative
pieces at successors, and intersects all previous derivatives at nonzero limits.
-/

open Cardinal Ordinal Set TopologicalSpace

universe u

namespace DescriptiveSetTheory

/-- The symmetric Hausdorff derivative associated with a set.-/
noncomputable def hausdorffDerivative {X : Type u} [TopologicalSpace X]
    (s : Set X) (i : Ordinal.{0}) : Set X :=
  Ordinal.limitRecOn i Set.univ
    (fun _ previous => closure (previous ∩ s) ∩ closure (previous ∩ sᶜ))
    (fun i _ previous => ⋂ j : Set.Iio i, previous j.1 j.2)

/--
@isnad1 id=eq.0h2v.s4.0b2b5ae1fe3f from=translated src=- shape=bd16de1a vocab=102507c0
-/
@[simp] theorem hausdorffDerivative_zero {X : Type u} [TopologicalSpace X] (s : Set X) :
    hausdorffDerivative s 0 = Set.univ := by
  simp [hausdorffDerivative]

/--
@isnad1 id=eq.0h3v.s6.2430ae97c6a1 from=translated src=- shape=7c5aff54 vocab=5b94d82c
-/
@[simp] theorem hausdorffDerivative_add_one {X : Type u} [TopologicalSpace X]
    (s : Set X) (i : Ordinal.{0}) :
    hausdorffDerivative s (i + 1) =
      closure (hausdorffDerivative s i ∩ s) ∩
        closure (hausdorffDerivative s i ∩ sᶜ) := by
  simp [hausdorffDerivative]

/--
@isnad1 id=eq.1h3v.s6.100f4411a477 from=translated src=- shape=6416f147 vocab=97b9ee98
-/
theorem hausdorffDerivative_of_isSuccLimit {X : Type u} [TopologicalSpace X]
    (s : Set X) {i : Ordinal.{0}} (hi : Order.IsSuccLimit i) :
    hausdorffDerivative s i = ⋂ j : Set.Iio i, hausdorffDerivative s j.1 := by
  simp [hausdorffDerivative, hi]

/-- Every Hausdorff derivative is closed.
@isnad1 id=isclosed.0h3v.s4.34fd5dc00520 from=translated src=- shape=1f30a21f vocab=ab0efea5
-/
theorem isClosed_hausdorffDerivative {X : Type u} [TopologicalSpace X]
    (s : Set X) (i : Ordinal.{0}) : IsClosed (hausdorffDerivative s i) := by
  induction i using Ordinal.limitRecOn with
  | zero => simp
  | add_one i ih =>
      rw [hausdorffDerivative_add_one]
      exact isClosed_closure.inter isClosed_closure
  | limit i hi ih =>
      rw [hausdorffDerivative_of_isSuccLimit s hi]
      exact isClosed_iInter fun j => ih j.1 j.2

/-- A successor derivative is contained in its predecessor.
@isnad1 id=le.0h3v.s5.ef394e4878a7 from=translated src=- shape=ecb648b0 vocab=b07ed51c
-/
theorem hausdorffDerivative_add_one_subset {X : Type u} [TopologicalSpace X]
    (s : Set X) (i : Ordinal.{0}) :
    hausdorffDerivative s (i + 1) ⊆ hausdorffDerivative s i := by
  rw [hausdorffDerivative_add_one]
  exact (inter_subset_left.trans
    (closure_minimal inter_subset_left (isClosed_hausdorffDerivative s i)))

/-- Hausdorff derivatives decrease with their ordinal index.
@isnad1 id=antitone.0h2v.s5.f6858a06a68c from=translated src=- shape=7b4eabd0 vocab=7480b101
-/
theorem antitone_hausdorffDerivative {X : Type u} [TopologicalSpace X]
    (s : Set X) : Antitone (hausdorffDerivative s) := by
  intro i k hik x hx
  induction k using WellFoundedLT.induction generalizing i x with
  | ind k ih =>
      rcases Ordinal.zero_or_succ_or_isSuccLimit k with rfl | hsucc | hlim
      · have hi : i = 0 := bot_unique hik
        subst i
        exact hx
      · obtain ⟨j, rfl⟩ := hsucc
        change i ≤ j + 1 at hik
        change x ∈ hausdorffDerivative s (j + 1) at hx
        by_cases hij : i ≤ j
        · exact ih j (Order.lt_succ j) hij
            (hausdorffDerivative_add_one_subset s j hx)
        · have hji : j < i := lt_of_not_ge hij
          have hjiSucc : j + 1 ≤ i := Order.add_one_le_iff.2 hji
          have hi : i = j + 1 := le_antisymm hik hjiSucc
          subst i
          exact hx
      · rcases eq_or_lt_of_le hik with rfl | hik'
        · exact hx
        · rw [hausdorffDerivative_of_isSuccLimit s hlim] at hx
          exact Set.mem_iInter.1 hx ⟨i, hik'⟩

/-- The initial segment below `ω₁` is not a countable type.
@isnad1 id=not.0h0v.s5.a028bc6c61d7 from=translated src=- shape=6817d759 vocab=b047e9f9
-/
theorem not_countable_Iio_omega_one : ¬Countable (Set.Iio (ω₁ : Ordinal)) := by
  intro h
  have hm : #(Set.Iio (ω₁ : Ordinal)) ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr h
  rw [Cardinal.mk_Iio_ordinal, Ordinal.card_omega] at hm
  exact Cardinal.aleph0_lt_aleph_one.2 (Cardinal.lift_le_aleph0.mp hm)

/-- A decreasing transfinite family of closed subsets of a second-countable space has a stationary
successor stage below `ω₁`.
@isnad1 id=ex.2h2v.s6.03cb595d1dfc from=translated src=- shape=68039a71 vocab=dfc3e6b7
-/
theorem exists_eq_add_one_of_antitone_isClosed {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] (H : Ordinal.{0} → Set X) (hH : Antitone H)
    (hClosed : ∀ i, IsClosed (H i)) :
    ∃ i : Ordinal.{0}, i < ω₁ ∧ H i = H (i + 1) := by
  classical
  let Drop := {i : Set.Iio (ω₁ : Ordinal) // H i.1 ≠ H (i.1 + 1)}
  have hdrop (d : Drop) : ∃ x, x ∈ H d.1.1 ∧ x ∉ H (d.1.1 + 1) := by
    have hsub : H (d.1.1 + 1) ⊆ H d.1.1 := hH (Order.le_succ d.1.1)
    have hnsub : ¬H d.1.1 ⊆ H (d.1.1 + 1) := by
      intro hreverse
      exact d.2 (Subset.antisymm hreverse hsub)
    exact Set.not_subset.1 hnsub
  choose x hxH hxNot using hdrop
  have hBasis (d : Drop) :
      ∃ U ∈ countableBasis X, x d ∈ U ∧ U ⊆ (H (d.1.1 + 1))ᶜ := by
    exact (isBasis_countableBasis X).exists_subset_of_mem_open (hxNot d)
      (hClosed (d.1.1 + 1)).isOpen_compl
  choose U hU_basis hxU hU_sub using hBasis
  let code : Drop → countableBasis X := fun d => ⟨U d, hU_basis d⟩
  have hcode : Function.Injective code := by
    intro d e hde
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Subtype.ext (Subtype.ext h))) with hlt | hgt
    · have hSuccLe : d.1.1 + 1 ≤ e.1.1 := Order.add_one_le_iff.2 hlt
      have hxeH : x e ∈ H (d.1.1 + 1) := hH hSuccLe (hxH e)
      have hxeNotU : x e ∉ U d := fun hmem => (hU_sub d hmem) hxeH
      have hUeq : U d = U e := congrArg Subtype.val hde
      exact hxeNotU (hUeq ▸ hxU e)
    · have hSuccLe : e.1.1 + 1 ≤ d.1.1 := Order.add_one_le_iff.2 hgt
      have hxdH : x d ∈ H (e.1.1 + 1) := hH hSuccLe (hxH d)
      have hxdNotU : x d ∉ U e := fun hmem => (hU_sub e hmem) hxdH
      have hUeq : U d = U e := congrArg Subtype.val hde
      exact hxdNotU (hUeq.symm ▸ hxU d)
  letI : Countable Drop := hcode.countable
  by_contra hnone
  push Not at hnone
  have hAllDrop : Function.Injective
      (fun i : Set.Iio (ω₁ : Ordinal) =>
        (⟨i, hnone i.1 i.2⟩ : Drop)) := by
    intro i j hij
    exact Subtype.ext (congrArg (fun d : Drop => d.1.1) hij)
  exact not_countable_Iio_omega_one hAllDrop.countable

/-- The Hausdorff derivative of every set has a stationary stage below `ω₁` in a
second-countable space.
@isnad1 id=ex.0h2v.s6.884af0aa6f48 from=translated src=- shape=726376a3 vocab=fa62b2b4
-/
theorem exists_hausdorffDerivative_eq_add_one {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] (s : Set X) :
    ∃ i : Ordinal.{0}, i < ω₁ ∧
      hausdorffDerivative s i = hausdorffDerivative s (i + 1) :=
  exists_eq_add_one_of_antitone_isClosed (hausdorffDerivative s)
    (antitone_hausdorffDerivative s) (isClosed_hausdorffDerivative s)

/-- For a `Δ⁰₂` set in a Polish space, a stationary Hausdorff derivative is empty.  The proof uses
the two closed covers supplied by the additive and multiplicative level-two descriptions and the
Baire theorem on the closed stationary derivative.
@isnad1 id=eq.2h3v.s6.c54dfc8cfdea from=translated src=- shape=86a0af50 vocab=6335b3d7
-/
theorem hausdorffDerivative_eq_empty_of_eq_add_one {X : Type u} [TopologicalSpace X]
    [PolishSpace X] {s : Set X} (hs : OrdinalDelta0 2 s) {i : Ordinal.{0}}
    (hfix : hausdorffDerivative s i = hausdorffDerivative s (i + 1)) :
    hausdorffDerivative s i = ∅ := by
  classical
  let H : Set X := hausdorffDerivative s i
  have hHClosed : IsClosed H := isClosed_hausdorffDerivative s i
  by_contra hne
  have hHNonempty : H.Nonempty := Set.nonempty_iff_ne_empty.2 hne
  letI : Nonempty H := ⟨⟨hHNonempty.choose, hHNonempty.choose_spec⟩⟩
  letI : IsCompletelyMetrizableSpace H := hHClosed.isCompletelyMetrizableSpace
  let S : Set H := {x | x.1 ∈ s}
  let C : Set H := {x | x.1 ∈ sᶜ}
  have hHSubS : H ⊆ closure (H ∩ s) := by
    intro x hx
    have hx' : x ∈ hausdorffDerivative s (i + 1) := hfix ▸ hx
    rw [hausdorffDerivative_add_one] at hx'
    exact hx'.1
  have hHSubC : H ⊆ closure (H ∩ sᶜ) := by
    intro x hx
    have hx' : x ∈ hausdorffDerivative s (i + 1) := hfix ▸ hx
    rw [hausdorffDerivative_add_one] at hx'
    exact hx'.2
  have hvalS : ((fun x : H => x.1) '' S : Set X) = H ∩ s := by
    ext x
    simp [H, S, and_comm]
  have hvalC : ((fun x : H => x.1) '' C : Set X) = H ∩ sᶜ := by
    ext x
    simp [H, C, and_comm]
  have hSDense : Dense S := by
    rw [Subtype.dense_iff, hvalS]
    exact hHSubS
  have hCDense : Dense C := by
    rw [Subtype.dense_iff, hvalC]
    exact hHSubC
  obtain ⟨F, hFClosed, hFs⟩ := ordinalSigma0_two_iff_eq_iUnion_isClosed.1 hs.1
  have hsCompl : OrdinalSigma0 2 sᶜ := (ordinalSigma0_compl_iff_pi0 2 s).2 hs.2
  obtain ⟨G, hGClosed, hGs⟩ := ordinalSigma0_two_iff_eq_iUnion_isClosed.1 hsCompl
  let pieces : ℕ ⊕ ℕ → Set H
    | Sum.inl n => (fun x : H => x.1) ⁻¹' F n
    | Sum.inr n => (fun x : H => x.1) ⁻¹' G n
  have hPiecesClosed : ∀ q, IsClosed (pieces q) := by
    rintro (n | n)
    · exact (hFClosed n).preimage continuous_subtype_val
    · exact (hGClosed n).preimage continuous_subtype_val
  have hPiecesCover : ⋃ q, pieces q = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hxs : x.1 ∈ s
    · rw [hFs] at hxs
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxs
      exact ⟨Sum.inl n, hxn⟩
    · have hxc : x.1 ∈ sᶜ := hxs
      rw [hGs] at hxc
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxc
      exact ⟨Sum.inr n, hxn⟩
  obtain ⟨q, hq⟩ := nonempty_interior_of_iUnion_of_closed hPiecesClosed hPiecesCover
  rcases q with n | n
  · obtain ⟨x, hxC, hxInterior⟩ := hCDense.exists_mem_open isOpen_interior hq
    have hxPiece : x ∈ pieces (Sum.inl n) := interior_subset hxInterior
    have hxF : x.1 ∈ F n := by
      change x.1 ∈ F n at hxPiece
      exact hxPiece
    have hxS : x.1 ∈ s := by
      rw [hFs]
      exact Set.mem_iUnion.2 ⟨n, hxF⟩
    exact hxC hxS
  · obtain ⟨x, hxS, hxInterior⟩ := hSDense.exists_mem_open isOpen_interior hq
    have hxPiece : x ∈ pieces (Sum.inr n) := interior_subset hxInterior
    have hxG : x.1 ∈ G n := by
      change x.1 ∈ G n at hxPiece
      exact hxPiece
    have hxC : x.1 ∈ sᶜ := by
      rw [hGs]
      exact Set.mem_iUnion.2 ⟨n, hxG⟩
    exact hxC hxS

/-- Every `Δ⁰₂` set in a Polish space has an empty Hausdorff derivative at some countable
ordinal.
@isnad1 id=ex.1h2v.s6.e379def1ea83 from=translated src=- shape=1992648a vocab=835e6a71
-/
theorem exists_hausdorffDerivative_eq_empty {X : Type u} [TopologicalSpace X]
    [PolishSpace X] {s : Set X} (hs : OrdinalDelta0 2 s) :
    ∃ i : Ordinal.{0}, i < ω₁ ∧ hausdorffDerivative s i = ∅ := by
  obtain ⟨i, hi, hfix⟩ := exists_hausdorffDerivative_eq_add_one s
  exact ⟨i, hi, hausdorffDerivative_eq_empty_of_eq_add_one hs hfix⟩

/-- The even open stage associated with a Hausdorff derivative.-/
def hausdorffEvenStage {X : Type u} [TopologicalSpace X]
    (s : Set X) (q : Ordinal.{0}) : Set X :=
  (closure (hausdorffDerivative s q ∩ s))ᶜ

/-- The odd open stage associated with a Hausdorff derivative.-/
def hausdorffOddStage {X : Type u} [TopologicalSpace X]
    (s : Set X) (q : Ordinal.{0}) : Set X :=
  (hausdorffDerivative s (q + 1))ᶜ

/-- The cumulative open family obtained by interleaving even and odd derivative stages.-/
def hausdorffDifferenceFamily {X : Type u} [TopologicalSpace X]
    (s : Set X) (i : Ordinal.{0}) : Set.Iio (2 * i) → Set X := fun j =>
  (⋃ q : Set.Iio i,
      if 2 * q.1 ≤ j.1 then hausdorffEvenStage s q.1 else ∅) ∪
    ⋃ q : Set.Iio i,
      if 2 * q.1 + 1 ≤ j.1 then hausdorffOddStage s q.1 else ∅

/--
@isnad1 id=iff.0h5v.s8.273642f239d2 from=translated src=- shape=d769ee7b vocab=5957d9cb
-/
theorem mem_hausdorffDifferenceFamily {X : Type u} [TopologicalSpace X]
    {s : Set X} {i : Ordinal.{0}} {j : Set.Iio (2 * i)} {x : X} :
    x ∈ hausdorffDifferenceFamily s i j ↔
      (∃ q : Set.Iio i, 2 * q.1 ≤ j.1 ∧ x ∈ hausdorffEvenStage s q.1) ∨
      ∃ q : Set.Iio i, 2 * q.1 + 1 ≤ j.1 ∧ x ∈ hausdorffOddStage s q.1 := by
  simp [hausdorffDifferenceFamily]

/--
@isnad1 id=monotone.0h3v.s6.cb266f79528d from=translated src=- shape=d34f47ac vocab=740bfd60
-/
theorem monotone_hausdorffDifferenceFamily {X : Type u} [TopologicalSpace X]
    (s : Set X) (i : Ordinal.{0}) : Monotone (hausdorffDifferenceFamily s i) := by
  intro j k hjk x hx
  rcases mem_hausdorffDifferenceFamily.1 hx with ⟨q, hqj, hxq⟩ | ⟨q, hqj, hxq⟩
  · exact mem_hausdorffDifferenceFamily.2 <| Or.inl ⟨q, hqj.trans hjk, hxq⟩
  · exact mem_hausdorffDifferenceFamily.2 <| Or.inr ⟨q, hqj.trans hjk, hxq⟩

/--
@isnad1 id=isopen.0h4v.s5.4e854f954293 from=translated src=- shape=e8784012 vocab=5c2afcf7
-/
theorem isOpen_hausdorffDifferenceFamily {X : Type u} [TopologicalSpace X]
    (s : Set X) (i : Ordinal.{0}) (j : Set.Iio (2 * i)) :
    IsOpen (hausdorffDifferenceFamily s i j) := by
  apply IsOpen.union
  · apply isOpen_iUnion
    intro q
    split_ifs
    · exact isClosed_closure.isOpen_compl
    · exact isOpen_empty
  · apply isOpen_iUnion
    intro q
    split_ifs
    · exact (isClosed_hausdorffDerivative s (q.1 + 1)).isOpen_compl
    · exact isOpen_empty

/-- Before an empty derivative stage, every point exits at a successor stage.
@isnad1 id=ex.1h4v.s6.7e919ccb5532 from=translated src=- shape=a4bacf03 vocab=d7446774
-/
theorem exists_hausdorffDerivative_exit {X : Type u} [TopologicalSpace X]
    {s : Set X} {i : Ordinal.{0}} {x : X} (hx : x ∉ hausdorffDerivative s i) :
    ∃ q : Ordinal.{0}, q < i ∧ x ∈ hausdorffDerivative s q ∧
      x ∉ hausdorffDerivative s (q + 1) := by
  classical
  obtain ⟨d, hd, hmin⟩ :=
    wellFounded_lt.has_min {j : Ordinal.{0} | x ∉ hausdorffDerivative s j} ⟨i, hx⟩
  have hdi : d ≤ i := le_of_not_gt (hmin i hx)
  rcases Ordinal.zero_or_succ_or_isSuccLimit d with rfl | ⟨q, rfl⟩ | hdlim
  · simp at hd
  · have hqMem : x ∈ hausdorffDerivative s q := by
      by_contra hq
      exact hmin q hq (Order.lt_succ q)
    exact ⟨q, (Order.lt_succ q).trans_le hdi, hqMem, hd⟩
  · change x ∉ hausdorffDerivative s d at hd
    rw [hausdorffDerivative_of_isSuccLimit s hdlim] at hd
    simp only [Set.mem_iInter] at hd
    push Not at hd
    obtain ⟨j, hj⟩ := hd
    exact (hmin j.1 hj j.2).elim

private theorem two_mul_lt_two_mul {q r : Ordinal.{0}} (hqr : q < r) :
    2 * q < 2 * r := by
  exact mul_lt_mul_of_pos_left hqr (by norm_num)

private theorem two_mul_add_one_lt_two_mul_add_one_iff (q r : Ordinal.{0}) :
    2 * q + 1 < 2 * r + 1 ↔ q < r := by
  change Order.succ (2 * q) < Order.succ (2 * r) ↔ q < r
  rw [Order.succ_lt_succ_iff]
  exact (mul_lt_mul_iff_right₀ (by norm_num : (0 : Ordinal) < 2))

private theorem le_of_two_mul_lt_two_mul_add_one {q r : Ordinal.{0}}
    (h : 2 * q < 2 * r + 1) : q ≤ r := by
  apply le_of_not_gt
  intro hrq
  have hmul : 2 * r < 2 * q := two_mul_lt_two_mul hrq
  have hle : 2 * r + 1 ≤ 2 * q := Order.add_one_le_iff.2 hmul
  exact (not_lt_of_ge hle) h

private theorem two_mul_add_one_lt {q i : Ordinal.{0}} (hqi : q < i) :
    2 * q + 1 < 2 * i := by
  have hqSucc : q + 1 ≤ i := Order.add_one_le_iff.2 hqi
  have hstage : 2 * q + 1 < 2 * (q + 1) := by
    rw [mul_add_one]
    exact (add_lt_add_iff_left (2 * q)).2 (by norm_num)
  exact hstage.trans_le (mul_le_mul_right hqSucc 2)

private theorem two_mul_lt_omega_one {i : Ordinal.{0}} (hi : i < ω₁) :
    2 * i < ω₁ := by
  rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_mul,
    Cardinal.lt_aleph_one_iff]
  have hi' : i.card ≤ ℵ₀ :=
    Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp hi)
  calc
    (2 : Ordinal).card * i.card ≤ ℵ₀ * ℵ₀ :=
      mul_le_mul' (by simp) hi'
    _ = ℵ₀ := Cardinal.aleph0_mul_aleph0

/-- An empty derivative produces an exact Hausdorff difference representation.
@isnad1 id=eq.1h3v.s5.dd7cdb31c501 from=translated src=- shape=60bab4dc vocab=4edc85e6
-/
theorem difference_hausdorffDifferenceFamily {X : Type u} [TopologicalSpace X]
    {s : Set X} {i : Ordinal.{0}} (hi : hausdorffDerivative s i = ∅) :
    difference (2 * i) (hausdorffDifferenceFamily s i) = s := by
  ext x
  constructor
  · intro hx
    rw [mem_difference] at hx
    obtain ⟨j, hjParity, hxj, hjLeast⟩ := hx
    rcases mem_hausdorffDifferenceFamily.1 hxj with
      ⟨q, hqj, hxEven⟩ | ⟨q, hqj, hxOdd⟩
    · have hjStage : j.1 ≤ 2 * q.1 := by
        apply le_of_not_gt
        intro hstagej
        let k : Set.Iio j.1 := ⟨2 * q.1, hstagej⟩
        have hxk : x ∈ hausdorffDifferenceFamily s i
            ⟨k.1, (show k.1 < j.1 from k.2).trans
              (show j.1 < 2 * i from j.2)⟩ :=
          mem_hausdorffDifferenceFamily.2 <| Or.inl ⟨q, le_rfl, hxEven⟩
        exact (hjLeast k) (by simpa [k] using hxk)
      have hjEq : j.1 = 2 * q.1 := le_antisymm hjStage hqj
      have hsame : ordinalParity j.1 = ordinalParity (2 * i) := by
        simp [hjEq]
      exact (hjParity hsame).elim
    · have hjStage : j.1 ≤ 2 * q.1 + 1 := by
        apply le_of_not_gt
        intro hstagej
        let k : Set.Iio j.1 := ⟨2 * q.1 + 1, hstagej⟩
        have hxk : x ∈ hausdorffDifferenceFamily s i
            ⟨k.1, (show k.1 < j.1 from k.2).trans
              (show j.1 < 2 * i from j.2)⟩ :=
          mem_hausdorffDifferenceFamily.2 <| Or.inr ⟨q, le_rfl, hxOdd⟩
        exact (hjLeast k) (by simpa [k] using hxk)
      have hjEq : j.1 = 2 * q.1 + 1 := le_antisymm hjStage hqj
      have hevenLt : 2 * q.1 < j.1 := by
        rw [hjEq]
        exact Order.lt_succ (2 * q.1)
      let k : Set.Iio j.1 := ⟨2 * q.1, hevenLt⟩
      have hxNotEvenFamily := hjLeast k
      have hxNotEven : x ∉ hausdorffEvenStage s q.1 := by
        intro hxEven
        apply hxNotEvenFamily
        exact mem_hausdorffDifferenceFamily.2 <| Or.inl ⟨q, le_rfl, hxEven⟩
      have hxClosure : x ∈ closure (hausdorffDerivative s q.1 ∩ s) := by
        simpa [hausdorffEvenStage] using hxNotEven
      have hxNotSucc : x ∉ hausdorffDerivative s (q.1 + 1) := by
        simpa [hausdorffOddStage] using hxOdd
      by_contra hxs
      have hxH : x ∈ hausdorffDerivative s q.1 :=
        closure_minimal inter_subset_left
          (isClosed_hausdorffDerivative s q.1) hxClosure
      have hxComplClosure :
          x ∈ closure (hausdorffDerivative s q.1 ∩ sᶜ) :=
        subset_closure ⟨hxH, hxs⟩
      apply hxNotSucc
      rw [hausdorffDerivative_add_one]
      exact ⟨hxClosure, hxComplClosure⟩
  · intro hxs
    have hxi : x ∉ hausdorffDerivative s i := by
      rw [hi]
      simp
    obtain ⟨q, hqi, hxH, hxNotSucc⟩ := exists_hausdorffDerivative_exit hxi
    let j : Set.Iio (2 * i) := ⟨2 * q + 1, two_mul_add_one_lt hqi⟩
    rw [mem_difference]
    refine ⟨j, by simp [j], ?_, ?_⟩
    · exact mem_hausdorffDifferenceFamily.2 <|
        Or.inr ⟨⟨q, hqi⟩, le_rfl, by simpa [hausdorffOddStage] using hxNotSucc⟩
    · intro k hxk
      have hkStage : k.1 < 2 * q + 1 := by
        have hk := k.2
        change k.1 < j.1 at hk
        simpa only [j] using hk
      rcases mem_hausdorffDifferenceFamily.1 hxk with
        ⟨r, hrk, hxEven⟩ | ⟨r, hrk, hxOdd⟩
      · have hrq : r.1 ≤ q :=
          le_of_two_mul_lt_two_mul_add_one (hrk.trans_lt hkStage)
        have hxHr : x ∈ hausdorffDerivative s r.1 :=
          antitone_hausdorffDerivative s hrq hxH
        exact hxEven (subset_closure ⟨hxHr, hxs⟩)
      · have hstage : 2 * r.1 + 1 < 2 * q + 1 := hrk.trans_lt hkStage
        have hrq : r.1 < q :=
          (two_mul_add_one_lt_two_mul_add_one_iff r.1 q).1 hstage
        have hrSuccLe : r.1 + 1 ≤ q := Order.add_one_le_iff.2 hrq
        exact hxOdd (antitone_hausdorffDerivative s hrSuccLe hxH)

/-- Every `Δ⁰₂` subset of a Polish space belongs to a countable exact Hausdorff
difference level over open sets.
@isnad1 id=ex.1h2v.s5.c67d6949788c from=translated src=- shape=0e2b33b6 vocab=ffa897e2
-/
theorem exists_hausdorffDifference_of_ordinalDelta0_two
    {X : Type u} [TopologicalSpace X] [PolishSpace X] {s : Set X}
    (hs : OrdinalDelta0 2 s) :
    ∃ i : Ordinal.{0}, HausdorffDifference i s := by
  obtain ⟨i, hiCount, hiEmpty⟩ := exists_hausdorffDerivative_eq_empty hs
  by_cases hi0 : i = 0
  · subst i
    have hUniv : (Set.univ : Set X) = ∅ := by
      simpa using hiEmpty
    have hsEmpty : s = ∅ := by
      apply Set.Subset.antisymm
      · intro x hx
        have hxUniv : x ∈ (Set.univ : Set X) := Set.mem_univ x
        rw [hUniv] at hxUniv
        exact hxUniv
      · exact Set.empty_subset s
    let A : Set.Iio (1 : Ordinal) → Set X := fun _ => ∅
    refine ⟨(1 : Ordinal), by norm_num,
      (by simpa using (isCountableBorelLevel_nat 1)), A,
      monotone_const, fun _ => isOpen_empty, ?_⟩
    rw [difference_one]
    simp [A, hsEmpty]
  · have hiPos : 0 < i := pos_iff_ne_zero.2 hi0
    refine ⟨2 * i, mul_pos (by norm_num) hiPos,
      two_mul_lt_omega_one hiCount,
      hausdorffDifferenceFamily s i,
      monotone_hausdorffDifferenceFamily s i,
      isOpen_hausdorffDifferenceFamily s i, ?_⟩
    exact difference_hausdorffDifferenceFamily hiEmpty

/-- Hausdorff--Kuratowski at level two: the ambiguous level-two Borel sets are exactly the
countable Hausdorff differences of open sets.
@isnad1 id=iff.0h2v.s5.1cd8c3c4ac0a from=translated src=- shape=e22acde7 vocab=ffa897e2
-/
theorem ordinalDelta0_two_iff_exists_hausdorffDifference
    {X : Type u} [TopologicalSpace X] [PolishSpace X] {s : Set X} :
    OrdinalDelta0 2 s ↔ ∃ i : Ordinal.{0}, HausdorffDifference i s := by
  constructor
  · exact exists_hausdorffDifference_of_ordinalDelta0_two
  · rintro ⟨i, hi⟩
    exact hi.ordinalDelta0_two

end DescriptiveSetTheory
