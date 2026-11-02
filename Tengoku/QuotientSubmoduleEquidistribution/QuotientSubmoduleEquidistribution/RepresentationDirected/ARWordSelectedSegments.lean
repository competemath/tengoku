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

@[simp] theorem originalPosition_mem {Q : List L}
    (C : Finset (Fin Q.length)) (x : Fin C.card) :
    originalPosition C x ∈ C :=
  C.orderEmbOfFin_mem rfl x

theorem originalPosition_lt_iff {Q : List L}
    (C : Finset (Fin Q.length)) (x y : Fin C.card) :
    originalPosition C x < originalPosition C y ↔ x < y :=
  (originalPosition C).lt_iff_lt

/-- Every selected original position has a unique position in the selected
word.-/
def selectedIndex {Q : List L} (C : Finset (Fin Q.length))
    (x : Fin Q.length) (hx : x ∈ C) : Fin C.card :=
  (C.orderIsoOfFin rfl).symm ⟨x, hx⟩

@[simp] theorem originalPosition_selectedIndex {Q : List L}
    (C : Finset (Fin Q.length)) (x : Fin Q.length) (hx : x ∈ C) :
    originalPosition C (selectedIndex C x hx) = x := by
  exact congrArg Subtype.val ((C.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)

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
labels.-/
@[simp] theorem map_projectLabel_segmentWord (Q : List L)
    (C : Finset (Fin Q.length)) :
    (segmentWord Q C).map projectLabel = selectedWord Q C := by
  simp [segmentWord, selectedWord, projectLabel, segmentKeyAt,
    Function.comp_def]

@[simp] theorem segmentWord_length (Q : List L)
    (C : Finset (Fin Q.length)) :
    (segmentWord Q C).length = C.card := by
  simp [segmentWord]

/-- Regard a position of the literal segment word as a selected position of
the original word.-/
def positionInOriginal (Q : List L) (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) : Fin Q.length :=
  originalPosition C (Fin.cast (segmentWord_length Q C) x)

@[simp] theorem positionInOriginal_mem (Q : List L)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    positionInOriginal Q C x ∈ C := by
  exact originalPosition_mem C _

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

@[simp] theorem positionInOriginal_positionOfSelected (Q : List L)
    (C : Finset (Fin Q.length)) (x : Fin Q.length) (hx : x ∈ C) :
    positionInOriginal Q C (positionOfSelected Q C x hx) = x := by
  simp [positionInOriginal, positionOfSelected]

@[simp] theorem positionOfSelected_positionInOriginal (Q : List L)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    positionOfSelected Q C (positionInOriginal Q C x)
      (positionInOriginal_mem Q C x) = x := by
  apply Fin.eq_of_val_eq
  simp [positionOfSelected, positionInOriginal]

theorem positionOfSelected_lt_iff (Q : List L)
    (C : Finset (Fin Q.length))
    {x y : Fin Q.length} (hx : x ∈ C) (_hy : y ∈ C) :
    positionOfSelected Q C x hx < positionOfSelected Q C y _hy ↔ x < y := by
  rw [← positionInOriginal_lt_iff Q C]
  simp

/-- Oriented equality criterion for canonical segment labels.-/
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
right of every selected point in that segment.-/
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
segment lies to the left of every selected point in that segment.-/
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
label are separated by an omitted occurrence of that label.-/
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
