import Tengoku.Seed.Data.Finset.Sort
import Tengoku.Seed.Data.Set.Finite.Range
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordCombinatorics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Selected consecutive segments in a finite labelled word

This file formalizes the finite-word content of
`lem:directed-segment-windows`.  No representation-theoretic example or
classification enters this file.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord.SelectedSegments

universe u

variable {L : Type u}

/-- The increasing embedding of the selected-word positions into the
positions of the original word.-/
def originalPosition {Q : List L}
    (C : Finset (Fin Q.length)) : Fin C.card ↪o Fin Q.length :=
  C.orderEmbOfFin rfl

/--
@isnad1 id=mem.0h4v.s6.f04538dcd4bb from=translated src=- shape=5a82f57a vocab=dfeaff88
-/
@[simp] theorem originalPosition_mem {Q : List L}
    (C : Finset (Fin Q.length)) (x : Fin C.card) :
    originalPosition C x ∈ C :=
  C.orderEmbOfFin_mem rfl x

/--
@isnad1 id=iff.0h5v.s7.f114888a7ef9 from=translated src=- shape=a23de3c1 vocab=24371345
-/
theorem originalPosition_lt_iff {Q : List L}
    (C : Finset (Fin Q.length)) (x y : Fin C.card) :
    originalPosition C x < originalPosition C y ↔ x < y :=
  (originalPosition C).lt_iff_lt

/-- Every selected original position has a unique position in the selected
word.-/
def selectedIndex {Q : List L} (C : Finset (Fin Q.length))
    (x : Fin Q.length) (hx : x ∈ C) : Fin C.card :=
  (C.orderIsoOfFin rfl).symm ⟨x, hx⟩

/--
@isnad1 id=eq.1h4v.s6.0fb65c5c2fa3 from=translated src=- shape=4b8b524a vocab=5b95b081
-/
@[simp] theorem originalPosition_selectedIndex {Q : List L}
    (C : Finset (Fin Q.length)) (x : Fin Q.length) (hx : x ∈ C) :
    originalPosition C (selectedIndex C x hx) = x := by
  exact congrArg Subtype.val ((C.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)

/--
@isnad1 id=eq.0h4v.s6.650a2abe2f8a from=translated src=- shape=1c8f5af6 vocab=1d41f68f
-/
@[simp] theorem selectedIndex_originalPosition {Q : List L}
    (C : Finset (Fin Q.length)) (x : Fin C.card) :
    selectedIndex C (originalPosition C x) (originalPosition_mem C x) = x := by
  exact (C.orderIsoOfFin rfl).symm_apply_apply x

/-- The set of omitted occurrences of the label of `x` which precede `x`.
This set, together with the original label, is a canonical name for the
selected consecutive segment containing `x`.-/
def omittedPrefix {Q : List L} (C : Finset (Fin Q.length))
    (x : Fin Q.length) : Set (Fin Q.length) :=
  {z | z < x ∧ ARWord.label Q z = ARWord.label Q x ∧ z ∉ C}

/-- A raw key for a selected segment.  The exact segment type below retains
only keys which are realized by selected positions.-/
abbrev SegmentKey (Q : List L) := L × Set (Fin Q.length)

def segmentKeyAt {Q : List L} (C : Finset (Fin Q.length))
    (x : Fin Q.length) : SegmentKey Q :=
  (ARWord.label Q x, omittedPrefix C x)

/-- The finite set of segment keys actually realized by the selection.-/
def realizedSegmentKeys (Q : List L) (C : Finset (Fin Q.length)) :
    Set (SegmentKey Q) :=
  Set.range fun x : Fin C.card ↦ segmentKeyAt C (originalPosition C x)

/-- Exact selected-segment labels.  This subtype has one point for every
maximal consecutive selected segment and no unused isolated points.-/
abbrev SegmentLabel (Q : List L) (C : Finset (Fin Q.length)) :=
  {A : SegmentKey Q // A ∈ realizedSegmentKeys Q C}

noncomputable instance segmentLabelFintype (Q : List L)
    (C : Finset (Fin Q.length)) : Fintype (SegmentLabel Q C) :=
  (Set.finite_range
    (fun x : Fin C.card ↦ segmentKeyAt C (originalPosition C x))).fintype

/-- Projection of an exact segment label back to its original label.-/
def projectLabel {Q : List L} {C : Finset (Fin Q.length)} :
    SegmentLabel Q C → L := fun A ↦ A.1.1

/-- The selected subword, relabelled by its maximal selected consecutive
segments.-/
def segmentWord (Q : List L) (C : Finset (Fin Q.length)) :
    List (SegmentLabel Q C) :=
  List.ofFn fun x : Fin C.card ↦
    ⟨segmentKeyAt C (originalPosition C x), ⟨x, rfl⟩⟩

/-- The same selected word with its original labels.-/
def selectedWord (Q : List L) (C : Finset (Fin Q.length)) : List L :=
  List.ofFn fun x : Fin C.card ↦ ARWord.label Q (originalPosition C x)

/-- Projecting segment labels recovers the selected subword with its original
labels.
@isnad1 id=eq.0h3v.s5.32c9577dd20d from=translated src=- shape=0747a6a0 vocab=1f49d9f7
-/
@[simp] theorem map_projectLabel_segmentWord (Q : List L)
    (C : Finset (Fin Q.length)) :
    (segmentWord Q C).map projectLabel = selectedWord Q C := by
  simp [segmentWord, selectedWord, projectLabel, segmentKeyAt,
    Function.comp_def]

/--
@isnad1 id=eq.0h3v.s4.938cea3997bd from=translated src=- shape=f2a65455 vocab=1a2b03aa
-/
@[simp] theorem segmentWord_length (Q : List L)
    (C : Finset (Fin Q.length)) :
    (segmentWord Q C).length = C.card := by
  simp [segmentWord]

/-- Regard a position of the literal segment word as a selected position of
the original word.-/
def positionInOriginal (Q : List L) (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) : Fin Q.length :=
  originalPosition C (Fin.cast (segmentWord_length Q C) x)

/--
@isnad1 id=mem.0h4v.s5.bea7b2358fbd from=translated src=- shape=74fd1ae5 vocab=6d07659e
-/
@[simp] theorem positionInOriginal_mem (Q : List L)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    positionInOriginal Q C x ∈ C := by
  exact originalPosition_mem C _

/--
@isnad1 id=iff.0h5v.s6.64bbb010ddf3 from=translated src=- shape=91fef507 vocab=a84bd4f6
-/
theorem positionInOriginal_lt_iff (Q : List L)
    (C : Finset (Fin Q.length))
    (x y : Fin (segmentWord Q C).length) :
    positionInOriginal Q C x < positionInOriginal Q C y ↔ x < y := by
  rw [positionInOriginal, positionInOriginal, originalPosition_lt_iff]
  simp

/-- The literal segment-word position occupied by a selected original
position.-/
def positionOfSelected (Q : List L) (C : Finset (Fin Q.length))
    (x : Fin Q.length) (hx : x ∈ C) :
    Fin (segmentWord Q C).length :=
  Fin.cast (segmentWord_length Q C).symm (selectedIndex C x hx)

/--
@isnad1 id=eq.1h4v.s5.95df431d0d58 from=translated src=- shape=0455d0f3 vocab=f6cb668b
-/
@[simp] theorem positionInOriginal_positionOfSelected (Q : List L)
    (C : Finset (Fin Q.length)) (x : Fin Q.length) (hx : x ∈ C) :
    positionInOriginal Q C (positionOfSelected Q C x hx) = x := by
  simp [positionInOriginal, positionOfSelected]

/--
@isnad1 id=eq.0h4v.s5.8e044561b655 from=translated src=- shape=00ba9a7d vocab=e3398c25
-/
@[simp] theorem positionOfSelected_positionInOriginal (Q : List L)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    positionOfSelected Q C (positionInOriginal Q C x)
      (positionInOriginal_mem Q C x) = x := by
  apply Fin.eq_of_val_eq
  simp [positionOfSelected, positionInOriginal]

/--
@isnad1 id=iff.2h5v.s6.76f2a0f6302d from=translated src=- shape=26767a6f vocab=744f664c
-/
theorem positionOfSelected_lt_iff (Q : List L)
    (C : Finset (Fin Q.length))
    {x y : Fin Q.length} (hx : x ∈ C) (_hy : y ∈ C) :
    positionOfSelected Q C x hx < positionOfSelected Q C y _hy ↔ x < y := by
  rw [← positionInOriginal_lt_iff Q C]
  simp

/-- Oriented equality criterion for canonical segment labels.
@isnad1 id=iff.3h5v.s7.741b6b37c1d6 from=translated src=- shape=1319f6d8 vocab=1c78b6bd
-/
theorem segmentKeyAt_eq_iff_of_lt {Q : List L}
    (C : Finset (Fin Q.length)) {x y : Fin Q.length}
    (hx : x ∈ C) (_hy : y ∈ C) (hxy : x < y) :
    segmentKeyAt C x = segmentKeyAt C y ↔
      ARWord.label Q x = ARWord.label Q y ∧
        ∀ z : Fin Q.length, x < z → z < y →
          ARWord.label Q z = ARWord.label Q x → z ∈ C := by
  constructor
  · intro h
    have hlabel : ARWord.label Q x = ARWord.label Q y :=
      congrArg Prod.fst h
    refine ⟨hlabel, ?_⟩
    intro z hxz hzy hzlabel
    by_contra hzC
    have hzyPrefix : z ∈ omittedPrefix C y := by
      exact ⟨hzy, hzlabel.trans hlabel, hzC⟩
    have hzxPrefix : z ∈ omittedPrefix C x := by
      simpa [segmentKeyAt] using
        congrArg (fun t : SegmentKey Q ↦ z ∈ t.2) h.symm ▸ hzyPrefix
    exact (not_lt_of_ge (le_of_lt hxz)) hzxPrefix.1
  · rintro ⟨hlabel, hall⟩
    apply Prod.ext hlabel
    ext z
    constructor
    · rintro ⟨hzx, hzlabel, hzC⟩
      exact ⟨hzx.trans hxy, hzlabel.trans hlabel, hzC⟩
    · rintro ⟨hzy, hzlabel, hzC⟩
      have hzlabelX : ARWord.label Q z = ARWord.label Q x :=
        hzlabel.trans hlabel.symm
      rcases lt_trichotomy z x with hzx | hzx | hxz
      · exact ⟨hzx, hzlabelX, hzC⟩
      · subst z
        exact False.elim (hzC hx)
      · exact False.elim (hzC (hall z hxz hzy hzlabelX))

/-- An omitted occurrence to the right of one point in a segment lies to the
right of every selected point in that segment.
@isnad1 id=lt.6h6v.s7.232c1c1f24aa from=translated src=- shape=1ac5a143 vocab=1c78b6bd
-/
theorem sameSegment_lt_omitted_right {Q : List L}
    (C : Finset (Fin Q.length)) {x u q : Fin Q.length}
    (_hx : x ∈ C) (hu : u ∈ C)
    (hxu : segmentKeyAt C x = segmentKeyAt C u)
    (hxq : x < q) (hqLabel : ARWord.label Q q = ARWord.label Q x)
    (hqC : q ∉ C) :
    u < q := by
  have hlabel : ARWord.label Q x = ARWord.label Q u :=
    congrArg Prod.fst hxu
  have hprefix : omittedPrefix C x = omittedPrefix C u :=
    congrArg Prod.snd hxu
  rcases lt_trichotomy u q with huq | huq | hqu
  · exact huq
  · subst q
    exact False.elim (hqC hu)
  · have hqU : q ∈ omittedPrefix C u :=
      ⟨hqu, hqLabel.trans hlabel, hqC⟩
    have hqX : q ∈ omittedPrefix C x := by
      rw [hprefix]
      exact hqU
    exact False.elim ((not_lt_of_ge (le_of_lt hxq)) hqX.1)

/-- Dually, an omitted occurrence to the left of one selected point in a
segment lies to the left of every selected point in that segment.
@isnad1 id=lt.6h6v.s7.be8a3834f6e5 from=translated src=- shape=9399d124 vocab=1c78b6bd
-/
theorem omitted_left_lt_sameSegment {Q : List L}
    (C : Finset (Fin Q.length)) {x u q : Fin Q.length}
    (_hx : x ∈ C) (hu : u ∈ C)
    (hxu : segmentKeyAt C x = segmentKeyAt C u)
    (hqx : q < x) (hqLabel : ARWord.label Q q = ARWord.label Q x)
    (hqC : q ∉ C) :
    q < u := by
  have hprefix : omittedPrefix C x = omittedPrefix C u :=
    congrArg Prod.snd hxu
  rcases lt_trichotomy q u with hqu | hqu | huq
  · exact hqu
  · subst q
    exact False.elim (hqC hu)
  · have hqX : q ∈ omittedPrefix C x :=
      ⟨hqx, hqLabel, hqC⟩
    have hqU : q ∈ omittedPrefix C u := by
      rw [← hprefix]
      exact hqX
    exact False.elim ((not_lt_of_ge (le_of_lt huq)) hqU.1)

/-- Different segment labels on selected occurrences of the same original
label are separated by an omitted occurrence of that label.
@isnad1 id=ex.5h5v.s7.07dc1d345668 from=translated src=- shape=9b764a60 vocab=1c78b6bd
-/
theorem exists_omitted_between_of_segmentKeyAt_ne {Q : List L}
    (C : Finset (Fin Q.length)) {x y : Fin Q.length}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x < y)
    (hlabel : ARWord.label Q x = ARWord.label Q y)
    (hne : segmentKeyAt C x ≠ segmentKeyAt C y) :
    ∃ q : Fin Q.length, x < q ∧ q < y ∧
      ARWord.label Q q = ARWord.label Q x ∧ q ∉ C := by
  classical
  by_contra hExists
  apply hne
  apply (segmentKeyAt_eq_iff_of_lt C hx hy hxy).2
  refine ⟨hlabel, ?_⟩
  intro q hxq hqy hqLabel
  by_contra hqC
  exact hExists ⟨q, hxq, hqy, hqLabel, hqC⟩

end QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord.SelectedSegments
