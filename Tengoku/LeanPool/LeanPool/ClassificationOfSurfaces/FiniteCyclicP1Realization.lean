/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicMoves
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.WeightedCircle
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.PolygonCellRadial
import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicSignedRealization
public import Tengoku

/-!
# Polygonal realization of Gallier--Xu P1

The boundary of every source face is assigned weight two at occurrences of the subdivided edge
and weight one everywhere else.  `WeightedCircle` turns those weights into the exact boundary
homeomorphism required by P1, and radial extension gives the corresponding disk homeomorphism.
-/

@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P1

@[simp] private theorem finCast_self {n : ℕ} (h : n = n) (i : Fin n) :
    Fin.cast h i = i := by
  apply Fin.ext
  rfl

@[simp] private theorem finCast_eq_mk {n m : ℕ} (h : n = m) (i : Fin n) :
    Fin.cast h i = ⟨i.val, h ▸ i.isLt⟩ :=
  rfl

@[simp] private theorem listGet_finCast {n : ℕ} {Type_ : Type*}
    (list : List Type_) (h : n = list.length) (i : Fin n) :
    list.get (Fin.cast h i) = list[i.val]'(h ▸ i.isLt) :=
  rfl

@[simp] private theorem listGetElem_finCast {n : ℕ} {Type_ : Type*}
    (list : List Type_) (h : n = list.length) (i : Fin n)
    (hi : (Fin.cast h i).val < list.length) (hj : i.val < list.length) :
    list[(Fin.cast h i).val]'hi = list[i.val]'hj :=
  rfl

/-- The number of target sides replacing one source dart. -/
def dartWeight {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) : ℕ :=
  if edgeOfDart d = a then 2 else 1

/-- The P1 subdivision weights around one face boundary. -/
def faceWeights (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    List ℕ :=
  (P.boundary f).map (dartWeight a)

/--
@isnad1 id=eq.0h3v.s4.a3fcf5d2ca3c from=translated src=- shape=6e5b5881 vocab=84f22ee2
-/
@[simp]
theorem faceWeights_length (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    (faceWeights P a f).length = (P.boundary f).length := by
  simp [faceWeights]

/--
@isnad1 id=positive.0h3v.s3.224e5172f852 from=translated src=- shape=3c29c769 vocab=43b0fa05
-/
theorem faceWeights_positive (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    WeightedCircle.Positive (faceWeights P a f) := by
  intro w hw
  rcases List.mem_map.1 hw with ⟨d, _hd, rfl⟩
  simp only [dartWeight]
  split <;> norm_num

/--
@isnad1 id=ne.1h3v.s4.33949ab0e4d2 from=translated src=- shape=7fe0789b vocab=bbe50fd5
-/
theorem faceWeights_ne_nil
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (validP : P.IsSurfaceValid) :
    faceWeights P a f ≠ [] := by
  simpa [faceWeights] using validP.2.1 f

/--
@isnad1 id=eq.0h3v.s5.9e6a213da21c from=translated src=- shape=91daed2e vocab=f1574ee1
-/
@[simp]
theorem length_expandDart_eq_dartWeight {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    (expandDart a d).length = dartWeight a d := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, dartWeight, edgeOfDart]
      · simp [expandDart, dartWeight, edgeOfDart, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, dartWeight, edgeOfDart]
      · simp [expandDart, dartWeight, edgeOfDart, h]

/--
@isnad1 id=eq.0h3v.s5.3b3813b5a069 from=translated src=- shape=ba395817 vocab=17d9f76a
-/
theorem expandWord_length_eq_sum_map_dartWeight {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    (expandWord a word).length = (word.map (dartWeight a)).sum := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      simp [expandWord, length_expandDart_eq_dartWeight]

/--
@isnad1 id=eq.0h3v.s5.a2f3979ea319 from=translated src=- shape=609d3de7 vocab=46049fe3
-/
theorem expandWord_length_eq_sum_faceWeights
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    (expandWord a (P.boundary f)).length = (faceWeights P a f).sum := by
  exact expandWord_length_eq_sum_map_dartWeight a (P.boundary f)

/--
@isnad1 id=eq.0h3v.s6.79bec9a58b7e from=translated src=- shape=90bab738 vocab=03466de7
-/
theorem faceWeights_sum
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    (faceWeights P a f).sum =
      ((expand P a).boundary (faceEquiv P a f)).length := by
  calc
    (faceWeights P a f).sum =
        (expandWord a (P.boundary f)).length :=
      (expandWord_length_eq_sum_faceWeights P a f).symm
    _ = ((expand P a).boundary (faceEquiv P a f)).length := by
      exact congrArg List.length (expand_boundary P a f).symm

/-- The first target side replacing source side `i`. -/
def expandedStartIndex
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    Fin ((expand P a).boundary (faceEquiv P a f)).length :=
  ⟨((faceWeights P a f).take i).sum, by
    rw [← faceWeights_sum P a f]
    exact WeightedCircle.sum_take_lt_sum
      (faceWeights_positive P a f) (Fin.cast (faceWeights_length P a f).symm i)⟩

/--
@isnad1 id=eq.0h4v.s6.abcb7970a344 from=translated src=- shape=6aaed857 vocab=734e3a42
-/
@[simp]
theorem expandedStartIndex_val
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (expandedStartIndex P a f i).val =
      ((faceWeights P a f).take i).sum :=
  rfl

/-- Transport a source occurrence to the first target occurrence in its expanded block. -/
def firstExpandedOccurrence
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (o : P.BoundaryOccurrence) :
    (expand P a).BoundaryOccurrence :=
  ⟨faceEquiv P a o.1, expandedStartIndex P a o.1 o.2⟩

/--
@isnad1 id=eq.0h4v.s7.b8b57d6fabe0 from=translated src=- shape=7bbcbca9 vocab=24342aa3
-/
theorem expandWord_getElem_expandedStart {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) (i : Fin word.length) :
    (expandWord a word)[((word.map (dartWeight a)).take i).sum]? =
      (expandDart a (word.get i))[0]? := by
  induction word with
  | nil => exact Fin.elim0 i
  | cons d word ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · cases d with
        | pos e =>
            by_cases he : e = a
            · subst e
              simp [expandWord, expandDart, dartWeight, edgeOfDart]
            · simp [expandWord, expandDart, dartWeight, edgeOfDart, he]
        | neg e =>
            by_cases he : e = a
            · subst e
              simp [expandWord, expandDart, dartWeight, edgeOfDart]
            · simp [expandWord, expandDart, dartWeight, edgeOfDart, he]
      · simp only [List.map_cons, Fin.val_succ, List.take_succ_cons,
          List.sum_cons, expandWord_cons, List.get_eq_getElem,
          List.getElem_cons_succ]
        rw [List.getElem?_append_right]
        · rw [length_expandDart_eq_dartWeight]
          simpa only [Nat.add_sub_cancel_left, List.get_eq_getElem] using ih j
        · rw [length_expandDart_eq_dartWeight]
          omega

/--
@isnad1 id=lt.0h3v.s5.511bbba992a4 from=translated src=- shape=34e2a062 vocab=2baec70c
-/
theorem expandDart_length_pos {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    0 < (expandDart a d).length := by
  rw [length_expandDart_eq_dartWeight]
  unfold dartWeight
  split <;> omega

/--
@isnad1 id=iff.0h3v.s4.79858323583a from=translated src=- shape=528e32f3 vocab=82e91f17
-/
@[simp]
theorem dartWeight_eq_two_iff {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    dartWeight a d = 2 ↔ edgeOfDart d = a := by
  simp [dartWeight]

/--
@isnad1 id=iff.0h3v.s4.a3d8b82e4d10 from=translated src=- shape=e2488c6b vocab=82e91f17
-/
@[simp]
theorem dartWeight_eq_one_iff {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    dartWeight a d = 1 ↔ edgeOfDart d ≠ a := by
  simp [dartWeight]

/-- More generally, lookup inside an expanded block agrees with lookup in the substituted
dart-word.
@isnad1 id=eq.1h5v.s8.c26d5d3ba672 from=translated src=- shape=37ee5f46 vocab=24342aa3
-/
theorem expandWord_getElem_expandedOffset {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) (i : Fin word.length)
    (k : ℕ) (hk : k < (expandDart a (word.get i)).length) :
    (expandWord a word)[
        ((word.map (dartWeight a)).take i).sum + k]? =
      (expandDart a (word.get i))[k]? := by
  induction word with
  | nil => exact Fin.elim0 i
  | cons d word ih =>
      induction i using Fin.cases with
      | zero =>
        simp only [List.map_cons, Fin.val_zero, List.take_zero, List.sum_nil,
          zero_add, expandWord_cons, List.get_eq_getElem, List.getElem_cons_zero]
        apply List.getElem?_append_left
        exact hk
      | succ j =>
        simp only [List.map_cons, Fin.val_succ, List.take_succ_cons,
          List.sum_cons, expandWord_cons, List.get_eq_getElem,
          List.getElem_cons_succ]
        rw [List.getElem?_append_right]
        · rw [length_expandDart_eq_dartWeight]
          simpa only [Nat.add_assoc, Nat.add_sub_cancel_left,
            List.get_eq_getElem] using ih j hk
        · rw [length_expandDart_eq_dartWeight]
          omega

/--
@isnad1 id=eq.0h3v.s6.9f3c0f8514d1 from=translated src=- shape=7ef7c31c vocab=59fd3cc3
-/
theorem firstExpandedOccurrence_dart
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (o : P.BoundaryOccurrence) :
    (firstExpandedOccurrence P a o).dart =
      (expandDart a o.dart).get
        ⟨0, expandDart_length_pos a o.dart⟩ := by
  rcases o with ⟨f, i⟩
  have hlookup :=
    expandWord_getElem_expandedStart a (P.boundary f) i
  have hstart :
      (((P.boundary f).map (dartWeight a)).take i).sum <
        (expandWord a (P.boundary f)).length := by
    rw [expandWord_length_eq_sum_faceWeights P a f]
    exact WeightedCircle.sum_take_lt_sum
      (faceWeights_positive P a f)
      (Fin.cast (faceWeights_length P a f).symm i)
  rw [List.getElem?_eq_getElem hstart,
    List.getElem?_eq_getElem (expandDart_length_pos a
      ((P.boundary f).get i))] at hlookup
  have hvalue := Option.some.inj hlookup
  simp only [firstExpandedOccurrence, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (expand_boundary P a f)]
  exact hvalue

/--
@isnad1 id=le.0h2v.s5.a7dd9c17c157 from=translated src=- shape=12a3d16b vocab=cd1260bc
-/
theorem sum_take_add_get_le_sum {weights : List ℕ}
    (i : Fin weights.length) :
    (weights.take i).sum + weights.get i ≤ weights.sum := by
  have hsplit :=
    congrArg List.sum (List.take_append_drop (i.val + 1) weights)
  rw [List.sum_append, List.take_succ_eq_append_getElem i.isLt,
    List.sum_append] at hsplit
  simp only [List.sum_singleton] at hsplit
  have hget : weights[i.val] = weights.get i := rfl
  rw [hget] at hsplit
  omega

/--
@isnad1 id=lt.1h2v.s5.43c0b9a1332f from=translated src=- shape=d39c058b vocab=16acde3c
-/
theorem sum_take_add_one_lt_sum_of_get_eq_two {weights : List ℕ}
    (i : Fin weights.length) (hget : weights.get i = 2) :
    (weights.take i).sum + 1 < weights.sum := by
  have hle := sum_take_add_get_le_sum i
  rw [hget] at hle
  omega

/-- A position in the concatenation of blocks whose lengths are `weights`. -/
abbrev BlockPosition (weights : List ℕ) :=
  Σ i : Fin weights.length, Fin (weights.get i)

/-- Linear position of a block-local index. -/
def blockPosition {weights : List ℕ} (p : BlockPosition weights) : ℕ :=
  (weights.take p.1).sum + p.2

/-- Distinct block-local positions have distinct linear positions.
@isnad1 id=injectiv.0h1v.s3.4dd9ccb75309 from=translated src=- shape=103a1916 vocab=60904e50
-/
@[simp] theorem blockPosition_injective (weights : List ℕ) :
    Function.Injective (@blockPosition weights) := by
  induction weights with
  | nil =>
      rintro ⟨i, _⟩
      exact Fin.elim0 i
  | cons w weights ih =>
      rintro ⟨i, k⟩ ⟨j, l⟩ heq
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero =>
              have hkl : k = l := by
                apply Fin.ext
                simpa [blockPosition] using heq
              subst l
              rfl
          | succ j =>
              exfalso
              have hk : k.val < w := k.isLt
              simp only [blockPosition, Fin.val_zero, List.take_zero,
                List.sum_nil, zero_add, Fin.val_succ,
                List.take_succ_cons, List.sum_cons] at heq
              omega
      | succ i =>
          induction j using Fin.cases with
          | zero =>
              exfalso
              have hl : l.val < w := l.isLt
              simp only [blockPosition, Fin.val_zero, List.take_zero,
                List.sum_nil, zero_add, Fin.val_succ,
                List.take_succ_cons, List.sum_cons] at heq
              omega
          | succ j =>
              have htail :
                  blockPosition (weights := weights) ⟨i, k⟩ =
                    blockPosition (weights := weights) ⟨j, l⟩ := by
                simp only [blockPosition, Fin.val_succ,
                  List.take_succ_cons, List.sum_cons] at heq ⊢
                omega
              have hp := ih htail
              cases hp
              rfl

/--
@isnad1 id=eq.0h4v.s5.c0ad634d16dc from=translated src=- shape=a5929075 vocab=17c8d232
-/
theorem faceWeights_get
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (faceWeights P a f).get
        (Fin.cast (faceWeights_length P a f).symm i) =
      dartWeight a ((P.boundary f).get i) := by
  unfold faceWeights
  simp

/-- A target-side index inside the expanded block of source side `i`. -/
def expandedOffsetIndex
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (k : Fin (dartWeight a ((P.boundary f).get i))) :
    Fin ((expand P a).boundary (faceEquiv P a f)).length :=
  ⟨((faceWeights P a f).take i).sum + k, by
    rw [← faceWeights_sum P a f]
    let i' : Fin (faceWeights P a f).length :=
      Fin.cast (faceWeights_length P a f).symm i
    have hle := sum_take_add_get_le_sum i'
    have hget :
        (faceWeights P a f).get i' =
          dartWeight a ((P.boundary f).get i) := by
      exact faceWeights_get P a f i
    change
      ((faceWeights P a f).take i).sum +
          (faceWeights P a f).get i' ≤
        (faceWeights P a f).sum at hle
    rw [hget] at hle
    omega⟩

/--
@isnad1 id=eq.0h5v.s7.00ee8b560707 from=translated src=- shape=950b1f14 vocab=8657fd1f
-/
@[simp]
theorem expandedOffsetIndex_val
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (k : Fin (dartWeight a ((P.boundary f).get i))) :
    (expandedOffsetIndex P a f i k).val =
      ((faceWeights P a f).take i).sum + k :=
  rfl

/-- A source occurrence together with one of the one or two target sides replacing it. -/
abbrev ExpandedSourcePosition
    (P : FiniteCyclicPresentation) (a : P.Edge) :=
  Σ o : P.BoundaryOccurrence, Fin (dartWeight a o.dart)

/-- Transport a block-local source position to its target boundary occurrence. -/
def expandedOccurrenceAt
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    (expand P a).BoundaryOccurrence :=
  ⟨faceEquiv P a p.1.1,
    expandedOffsetIndex P a p.1.1 p.1.2 p.2⟩

/-- The block-local occurrence transport is injective: expanded blocks never overlap.
@isnad1 id=injectiv.0h2v.s4.14f4acd02431 from=translated src=- shape=a53e6100 vocab=eada4d55
-/
theorem expandedOccurrenceAt_injective
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    Function.Injective (expandedOccurrenceAt P a) := by
  rintro ⟨⟨f, i⟩, k⟩ ⟨⟨g, j⟩, l⟩ h
  have hface : f = g := by
    apply (faceEquiv P a).injective
    exact congrArg Sigma.fst h
  subst g
  have hlinear :
      ((faceWeights P a f).take i).sum + k =
        ((faceWeights P a f).take j).sum + l := by
    exact congrArg (fun o => o.2.val) h
  let i' : Fin (faceWeights P a f).length :=
    Fin.cast (faceWeights_length P a f).symm i
  let j' : Fin (faceWeights P a f).length :=
    Fin.cast (faceWeights_length P a f).symm j
  let k' : Fin ((faceWeights P a f).get i') :=
    Fin.cast (faceWeights_get P a f i).symm k
  let l' : Fin ((faceWeights P a f).get j') :=
    Fin.cast (faceWeights_get P a f j).symm l
  have hblock :
      blockPosition (weights := faceWeights P a f) ⟨i', k'⟩ =
        blockPosition (weights := faceWeights P a f) ⟨j', l'⟩ := by
    exact hlinear
  have hpair :=
    blockPosition_injective (faceWeights P a f) hblock
  have hij' : i' = j' := congrArg Sigma.fst hpair
  have hij : i = j := by
    apply Fin.ext
    have hvals := congrArg Fin.val hij'
    change i.val = j.val at hvals
    exact hvals
  subst j
  have hkl : k = l := by
    apply Fin.ext
    simpa using hlinear
  subst l
  rfl

/--
@isnad1 id=eq.0h3v.s7.a5f4f41cebd1 from=translated src=- shape=31efe794 vocab=1be77625
-/
theorem expandedOccurrenceAt_dart
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    (expandedOccurrenceAt P a p).dart =
      (expandDart a p.1.dart).get
        (Fin.cast (length_expandDart_eq_dartWeight a p.1.dart).symm p.2) := by
  rcases p with ⟨⟨f, i⟩, k⟩
  let k' : Fin (expandDart a ((P.boundary f).get i)).length :=
    Fin.cast (length_expandDart_eq_dartWeight a _).symm k
  have hlookup :=
    expandWord_getElem_expandedOffset a (P.boundary f) i k'
      k'.isLt
  have hstart :
      (((P.boundary f).map (dartWeight a)).take i).sum + k <
        (expandWord a (P.boundary f)).length := by
    rw [expandWord_length_eq_sum_faceWeights P a f]
    change
      ((faceWeights P a f).take i).sum + k <
        (faceWeights P a f).sum
    let i' : Fin (faceWeights P a f).length :=
      Fin.cast (faceWeights_length P a f).symm i
    have hle := sum_take_add_get_le_sum i'
    change
      ((faceWeights P a f).take i).sum +
          (faceWeights P a f).get i' ≤
        (faceWeights P a f).sum at hle
    have hget :
        (faceWeights P a f).get i' =
          dartWeight a ((P.boundary f).get i) := by
      exact faceWeights_get P a f i
    rw [hget] at hle
    have hk :
        k.val < dartWeight a ((P.boundary f).get i) :=
      k.isLt
    omega
  have hstart' :
      (((P.boundary f).map (dartWeight a)).take i).sum + k' <
        (expandWord a (P.boundary f)).length := by
    exact hstart
  rw [List.getElem?_eq_getElem hstart',
    List.getElem?_eq_getElem k'.isLt] at hlookup
  have hvalue := Option.some.inj hlookup
  simp only [expandedOccurrenceAt, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (expand_boundary P a f)]
  exact hvalue

/--
@isnad1 id=iff.0h3v.s4.4cea9877c040 from=translated src=- shape=cfc154c4 vocab=bc44883c
-/
theorem isBoundaryEdge_expand_castSucc_iff
    (P : FiniteCyclicPresentation) (a e : P.Edge) :
    (expand P a).IsBoundaryEdge e.castSucc ↔
      P.IsBoundaryEdge e := by
  unfold IsBoundaryEdge
  rw [← edgeMultiplicity_expand_castSucc P a e]

/--
@isnad1 id=iff.0h2v.s4.b258cb02786c from=translated src=- shape=de2ee2c9 vocab=27764f58
-/
theorem isBoundaryEdge_expand_freshEdge_iff
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    (expand P a).IsBoundaryEdge (freshEdge P.edgeCount) ↔
      P.IsBoundaryEdge a := by
  unfold IsBoundaryEdge
  rw [← edgeMultiplicity_expand_freshEdge P a]

/-- The target edge at a block-local offset. -/
def expandedSubedge {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (k : Fin (dartWeight a d)) : Fin (n + 1) :=
  edgeOfDart
    ((expandDart a d)[k.val]'(by
      rw [length_expandDart_eq_dartWeight]
      exact k.isLt))

/-- Each target subedge has the same boundary/internal status as its source edge.
@isnad1 id=iff.0h4v.s5.ba617cfa2801 from=translated src=- shape=ef48a01f vocab=c8781754
-/
theorem isBoundaryEdge_expandedSubedge_iff
    (P : FiniteCyclicPresentation) (a : P.Edge) (d : P.Dart)
    (k : Fin (dartWeight a d)) :
    (expand P a).IsBoundaryEdge (expandedSubedge a d k) ↔
      P.IsBoundaryEdge (edgeOfDart d) := by
  cases d with
  | pos e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        interval_cases hkval : k.val <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            hkval, firstSubedge, isBoundaryEdge_expand_castSucc_iff,
            isBoundaryEdge_expand_freshEdge_iff]
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
          he, hk0, isBoundaryEdge_expand_castSucc_iff]
  | neg e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        interval_cases hkval : k.val <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            hkval, firstSubedge, isBoundaryEdge_expand_castSucc_iff,
            isBoundaryEdge_expand_freshEdge_iff]
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
          he, hk0, isBoundaryEdge_expand_castSucc_iff]

/-- Every target subedge has the same boundary/internal status as its source edge.
@isnad1 id=not.1h3v.s5.aed9a5f23835 from=translated src=- shape=b097ec8f vocab=c81fff0c
-/
theorem expandedOccurrenceAt_not_boundary
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a)
    (h : ¬P.IsBoundaryEdge p.1.edge) :
    ¬(expand P a).IsBoundaryEdge (expandedOccurrenceAt P a p).edge := by
  rw [BoundaryOccurrence.edge, expandedOccurrenceAt_dart]
  exact (isBoundaryEdge_expandedSubedge_iff P a p.1.dart p.2).not.mpr h

/-- The first local target-side offset always exists. -/
def zeroOffset {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) :
    Fin (dartWeight a d) :=
  ⟨0, by
    unfold dartWeight
    split <;> omega⟩

/-- A selected source side has a second local target-side offset. -/
def oneOffset {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (hselected : edgeOfDart d = a) :
    Fin (dartWeight a d) :=
  ⟨1, by
    rw [(dartWeight_eq_two_iff a d).2 hselected]
    omega⟩

/--
@isnad1 id=eq.0h3v.s4.9f399bab937e from=translated src=- shape=1f288bc9 vocab=bec85c1a
-/
@[simp]
theorem dartWeight_flip {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    dartWeight a d.flip = dartWeight a d := by
  cases d <;> rfl

/-- The signed target dart at a block-local offset. -/
def expandedSubdart {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (k : Fin (dartWeight a d)) : SignedDart (Fin (n + 1)) :=
  (expandDart a d)[k.val]'(by
    rw [length_expandDart_eq_dartWeight]
    exact k.isLt)

/-- Reverse a block-local offset after reversing the source dart. -/
def reverseOffset {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (k : Fin (dartWeight a d)) : Fin (dartWeight a d.flip) :=
  ⟨dartWeight a d - (k.val + 1), by
    rw [dartWeight_flip]
    exact Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) (Nat.succ_pos _)⟩

/-- Reversing a source dart reverses the expanded block and flips its signed darts.
@isnad1 id=eq.0h4v.s5.5ed06c33caa4 from=translated src=- shape=e3c4d53c vocab=c0748403
-/
theorem expandedSubdart_flip_reverseOffset {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) (k : Fin (dartWeight a d)) :
    expandedSubdart a d.flip (reverseOffset a d k) =
      (expandedSubdart a d k).flip := by
  cases d with
  | pos e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        interval_cases hkval : k.val <;>
          simp [expandedSubdart, reverseOffset, expandDart, dartWeight,
            edgeOfDart, hkval, SignedDart.flip]
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubdart, reverseOffset, expandDart, dartWeight,
          edgeOfDart, he, hk0, SignedDart.flip]
  | neg e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        interval_cases hkval : k.val <;>
          simp [expandedSubdart, reverseOffset, expandDart, dartWeight,
            edgeOfDart, hkval, SignedDart.flip]
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubdart, reverseOffset, expandDart, dartWeight,
          edgeOfDart, he, hk0, SignedDart.flip]

/--
@isnad1 id=eq.0h2v.s4.bcc89c7591f1 from=translated src=- shape=aeafb86d vocab=2650c1c2
-/
theorem BoundaryPairing.target_edge_eq_source_edge
    {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.target.edge = pairing.source.edge := by
  cases hdirection : pairing.direction with
  | same =>
      have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      simp only [BoundaryOccurrence.edge, hcompatible]
  | opposite =>
      have hcompatible :
          pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      simp only [BoundaryOccurrence.edge, hcompatible, edgeOfDart_flip]

/--
@isnad1 id=eq.0h3v.s5.855fd0d12968 from=translated src=- shape=d7a321a4 vocab=70765297
-/
theorem expandedOccurrenceAt_dart_eq_expandedSubdart
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    (expandedOccurrenceAt P a p).dart =
      expandedSubdart a p.1.dart p.2 := by
  exact expandedOccurrenceAt_dart P a p

/-- Transport a block-local offset across an equal-dart pairing. -/
def samePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) :
    Fin (dartWeight a pairing.target.dart) :=
  Fin.cast (congrArg (dartWeight a) hcompatible.symm) k

/-- Transport a block-local offset across a flipped-dart pairing. -/
def oppositePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) :
    Fin (dartWeight a pairing.target.dart) :=
  Fin.cast (congrArg (dartWeight a) hcompatible.symm)
    (reverseOffset a pairing.source.dart k)

/--
@isnad1 id=eq.1h5v.s5.894dcb435ae7 from=translated src=- shape=6fa0fa19 vocab=238d1cdc
-/
theorem expandedSubdart_cast_eq {n : ℕ} (a : Fin n)
    {d₁ d₂ : SignedDart (Fin n)} (h : d₂ = d₁)
    (k : Fin (dartWeight a d₁)) :
    expandedSubdart a d₂
        (Fin.cast (congrArg (dartWeight a) h.symm) k) =
      expandedSubdart a d₁ k := by
  subst d₂
  rfl

/--
@isnad1 id=eq.1h5v.s6.62c36a398d3a from=translated src=- shape=fafd7bd0 vocab=7b8d4aa5
-/
theorem expandedSubdart_cast_flip {n : ℕ} (a : Fin n)
    {d₁ d₂ : SignedDart (Fin n)} (h : d₂ = d₁.flip)
    (k : Fin (dartWeight a d₁)) :
    expandedSubdart a d₂
        (Fin.cast (congrArg (dartWeight a) h.symm)
          (reverseOffset a d₁ k)) =
      (expandedSubdart a d₁ k).flip := by
  subst d₂
  exact expandedSubdart_flip_reverseOffset a d₁ k

/--
@isnad1 id=eq.1h4v.s6.90e4219e1adc from=translated src=- shape=4a19bc30 vocab=f517d7bb
-/
theorem expandedSubdart_samePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) :
    expandedSubdart a pairing.target.dart
        (samePairedOffset a pairing hcompatible k) =
      expandedSubdart a pairing.source.dart k := by
  exact expandedSubdart_cast_eq a hcompatible k

/--
@isnad1 id=eq.1h4v.s6.21de1a3a147e from=translated src=- shape=9930322d vocab=5e182883
-/
theorem expandedSubdart_oppositePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) :
    expandedSubdart a pairing.target.dart
        (oppositePairedOffset a pairing hcompatible k) =
      (expandedSubdart a pairing.source.dart k).flip := by
  exact expandedSubdart_cast_flip a hcompatible k

/-- Each same-direction old pairing expands to corresponding target-subedge pairings. -/
noncomputable def expandedPairingSame
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) :
    (expand P a).BoundaryPairing where
  source := expandedOccurrenceAt P a ⟨pairing.source, k⟩
  target :=
    expandedOccurrenceAt P a
      ⟨pairing.target, samePairedOffset a pairing hcompatible k⟩
  source_ne_target := by
    intro heq
    have hp :=
      expandedOccurrenceAt_injective P a heq
    exact pairing.source_ne_target (congrArg Sigma.fst hp)
  source_not_boundary :=
    expandedOccurrenceAt_not_boundary P a
      ⟨pairing.source, k⟩ pairing.source_not_boundary
  target_not_boundary :=
    expandedOccurrenceAt_not_boundary P a
      ⟨pairing.target, samePairedOffset a pairing hcompatible k⟩
      pairing.target_not_boundary
  direction := .same
  compatible := by
    rw [expandedOccurrenceAt_dart_eq_expandedSubdart,
      expandedOccurrenceAt_dart_eq_expandedSubdart]
    exact expandedSubdart_samePairedOffset a pairing hcompatible k

/-- Each opposite-direction old pairing expands to reversed target-subedge pairings. -/
noncomputable def expandedPairingOpposite
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) :
    (expand P a).BoundaryPairing where
  source := expandedOccurrenceAt P a ⟨pairing.source, k⟩
  target :=
    expandedOccurrenceAt P a
      ⟨pairing.target, oppositePairedOffset a pairing hcompatible k⟩
  source_ne_target := by
    intro heq
    have hp :=
      expandedOccurrenceAt_injective P a heq
    exact pairing.source_ne_target (congrArg Sigma.fst hp)
  source_not_boundary :=
    expandedOccurrenceAt_not_boundary P a
      ⟨pairing.source, k⟩ pairing.source_not_boundary
  target_not_boundary :=
    expandedOccurrenceAt_not_boundary P a
      ⟨pairing.target, oppositePairedOffset a pairing hcompatible k⟩
      pairing.target_not_boundary
  direction := .opposite
  compatible := by
    rw [expandedOccurrenceAt_dart_eq_expandedSubdart,
      expandedOccurrenceAt_dart_eq_expandedSubdart]
    exact expandedSubdart_oppositePairedOffset a pairing hcompatible k

/-- The second target side replacing a selected source occurrence. -/
def secondExpandedIndex
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hselected : edgeOfDart ((P.boundary f).get i) = a) :
    Fin ((expand P a).boundary (faceEquiv P a f)).length :=
  ⟨((faceWeights P a f).take i).sum + 1, by
    rw [← faceWeights_sum P a f]
    let i' : Fin (faceWeights P a f).length :=
      Fin.cast (faceWeights_length P a f).symm i
    have hget : (faceWeights P a f).get i' = 2 := by
      rw [faceWeights_get]
      exact (dartWeight_eq_two_iff a _).2 hselected
    exact sum_take_add_one_lt_sum_of_get_eq_two i' hget⟩

/--
@isnad1 id=eq.1h4v.s6.c0c51ef5c601 from=translated src=- shape=c8337338 vocab=b691876c
-/
@[simp]
theorem secondExpandedIndex_val
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hselected : edgeOfDart ((P.boundary f).get i) = a) :
    (secondExpandedIndex P a f i hselected).val =
      ((faceWeights P a f).take i).sum + 1 :=
  rfl

/-- Transport a selected source occurrence to the second occurrence in its expanded block. -/
def secondExpandedOccurrence
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (o : P.BoundaryOccurrence) (hselected : o.edge = a) :
    (expand P a).BoundaryOccurrence :=
  ⟨faceEquiv P a o.1,
    secondExpandedIndex P a o.1 o.2 hselected⟩

/--
@isnad1 id=eq.1h3v.s6.2680bf76c2e2 from=translated src=- shape=4ec61f22 vocab=4515ac69
-/
theorem secondExpandedOccurrence_dart
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (o : P.BoundaryOccurrence) (hselected : o.edge = a) :
    (secondExpandedOccurrence P a o hselected).dart =
      (expandDart a o.dart).get
        ⟨1, by
          rw [length_expandDart_eq_dartWeight]
          rw [(dartWeight_eq_two_iff a o.dart).2 hselected]
          norm_num⟩ := by
  rcases o with ⟨f, i⟩
  have hk :
      1 < (expandDart a ((P.boundary f).get i)).length := by
    rw [length_expandDart_eq_dartWeight]
    have hw : dartWeight a ((P.boundary f).get i) = 2 :=
      (dartWeight_eq_two_iff a _).2 hselected
    omega
  have hlookup :=
    expandWord_getElem_expandedOffset a (P.boundary f) i 1 hk
  have hstart :
      (((P.boundary f).map (dartWeight a)).take i).sum + 1 <
        (expandWord a (P.boundary f)).length := by
    rw [expandWord_length_eq_sum_faceWeights P a f]
    let i' : Fin (faceWeights P a f).length :=
      Fin.cast (faceWeights_length P a f).symm i
    have hget : (faceWeights P a f).get i' = 2 := by
      rw [faceWeights_get]
      exact (dartWeight_eq_two_iff a _).2 hselected
    exact sum_take_add_one_lt_sum_of_get_eq_two i' hget
  rw [List.getElem?_eq_getElem hstart,
    List.getElem?_eq_getElem hk] at hlookup
  have hvalue := Option.some.inj hlookup
  simp only [secondExpandedOccurrence, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (expand_boundary P a f)]
  exact hvalue

/-- The exact weighted homeomorphism between the source and P1-expanded face boundaries. -/
noncomputable def faceCircleHomeomorph
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Circle ≃ₜ Circle :=
  WeightedCircle.circleHomeomorph
    (faceWeights P a f) (faceWeights_positive P a f)
    (faceWeights_ne_nil P a f validP)

/-- Radially extend the weighted boundary map to the whole face disk. -/
noncomputable def faceHomeomorph
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell (P.boundary f).length ≃ₜ
      PolygonCell ((expand P a).boundary (faceEquiv P a f)).length :=
  PolygonCell.radialHomeomorph (faceCircleHomeomorph P a validP f)

/-- P1 acts facewise on the polygonal pre-realization. -/
noncomputable def preHomeomorph
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    P.PolygonalPreRealization ≃ₜ (expand P a).PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap (faceEquiv P a).bijective
      (fun f => (faceHomeomorph P a validP f).isHomeomorph)).homeomorph
    (Sigma.map (faceEquiv P a) fun f => faceHomeomorph P a validP f)

/--
@isnad1 id=eq.1h3v.s8.62274aa63ffc from=translated src=- shape=c642ee58 vocab=265ae782
-/
@[simp]
theorem preHomeomorph_apply_fst
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (x : P.PolygonalPreRealization) :
    (preHomeomorph P a validP x).1 = faceEquiv P a x.1 :=
  rfl

/--
@isnad1 id=eq.1h4v.s9.f4fe15c45754 from=translated src=- shape=b9dae6d5 vocab=d188309b
-/
@[simp]
theorem faceHomeomorph_ofCircle
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face) (z : Circle) :
    faceHomeomorph P a validP f
        (PolygonCell.ofCircle (P.boundary f).length z) =
      PolygonCell.ofCircle
        ((expand P a).boundary (faceEquiv P a f)).length
        (faceCircleHomeomorph P a validP f z) := by
  exact PolygonCell.radialHomeomorph_ofCircle _ _

/-- Exact boundary-coordinate formula for the facewise P1 map.
@isnad1 id=eq.1h5v.s10.329c480e46b6 from=translated src=- shape=96ddf7ae vocab=7942a603
-/
theorem faceHomeomorph_side
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    faceHomeomorph P a validP f (PolygonCell.side i t) =
      PolygonCell.ofCircle
        ((expand P a).boundary (faceEquiv P a f)).length
        (Circle.exp
          (2 * Real.pi /
              ((expand P a).boundary (faceEquiv P a f)).length *
            (((faceWeights P a f).take i).sum +
              (faceWeights P a f).get
                  (Fin.cast (faceWeights_length P a f).symm i) *
                (t : ℝ)))) := by
  rw [show PolygonCell.side i t =
      PolygonCell.ofCircle (P.boundary f).length
        (Circle.exp
          (2 * Real.pi / (P.boundary f).length *
            ((i : ℝ) + (t : ℝ)))) by
    apply PolygonCell.ext
    change (Circle.exp (PolygonCell.sideAngle i t) : ℂ) =
      (Circle.exp
        (2 * Real.pi / (P.boundary f).length *
          ((i : ℝ) + (t : ℝ))) : Circle)
    congr 2
    unfold PolygonCell.sideAngle
    ring]
  rw [faceHomeomorph_ofCircle]
  apply congrArg (PolygonCell.ofCircle
    ((expand P a).boundary (faceEquiv P a f)).length)
  simpa only [faceCircleHomeomorph, faceWeights_length,
      faceWeights_sum, Fin.val_cast] using
    WeightedCircle.circleHomeomorph_exp_index_add'
      (faceWeights P a f) (faceWeights_positive P a f)
      (faceWeights_ne_nil P a f validP)
      (Fin.cast (faceWeights_length P a f).symm i) t

/--
@isnad1 id=eq.2h5v.s10.b523df25c376 from=translated src=- shape=3ffb3f9b vocab=35b5ede8
-/
theorem faceHomeomorph_side_of_not_selected
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hnot : edgeOfDart ((P.boundary f).get i) ≠ a)
    (t : unitInterval) :
    faceHomeomorph P a validP f (PolygonCell.side i t) =
      PolygonCell.side (expandedStartIndex P a f i) t := by
  rw [faceHomeomorph_side]
  apply PolygonCell.ext
  change
    (Circle.exp
      (2 * Real.pi /
          ((expand P a).boundary (faceEquiv P a f)).length *
        (((faceWeights P a f).take i).sum +
          (faceWeights P a f).get
              (Fin.cast (faceWeights_length P a f).symm i) *
            (t : ℝ))) : ℂ) =
      (Circle.exp
        (PolygonCell.sideAngle (expandedStartIndex P a f i) t) : ℂ)
  rw [faceWeights_get,
    (dartWeight_eq_one_iff a _).2 hnot]
  unfold PolygonCell.sideAngle
  rw [expandedStartIndex_val]
  push_cast
  ring

/-- Rescale the first half of a source side to a complete target side. -/
def firstHalfParameter (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    unitInterval :=
  ⟨2 * (t : ℝ), mul_nonneg (by norm_num) t.property.1, by linarith⟩

/-- Rescale the second half of a source side to a complete target side. -/
def secondHalfParameter (t : unitInterval) (h : 1 / 2 ≤ (t : ℝ)) :
    unitInterval :=
  ⟨2 * (t : ℝ) - 1, by linarith, by linarith [t.property.2]⟩

/--
@isnad1 id=eq.1h1v.s6.e480faf6bb96 from=translated src=- shape=0900396f vocab=593affab
-/
@[simp]
theorem firstHalfParameter_val (t : unitInterval)
    (h : (t : ℝ) ≤ 1 / 2) :
    (firstHalfParameter t h : ℝ) = 2 * (t : ℝ) :=
  rfl

/--
@isnad1 id=eq.1h1v.s6.e16267af57c5 from=translated src=- shape=3cfbe3e5 vocab=3e42dc5e
-/
@[simp]
theorem secondHalfParameter_val (t : unitInterval)
    (h : 1 / 2 ≤ (t : ℝ)) :
    (secondHalfParameter t h : ℝ) = 2 * (t : ℝ) - 1 :=
  rfl

/--
@isnad1 id=eq.3h5v.s10.8195ff867a30 from=translated src=- shape=51514751 vocab=4fbd8fed
-/
theorem faceHomeomorph_side_firstHalf
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hselected : edgeOfDart ((P.boundary f).get i) = a)
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    faceHomeomorph P a validP f (PolygonCell.side i t) =
      PolygonCell.side (expandedStartIndex P a f i)
        (firstHalfParameter t ht) := by
  rw [faceHomeomorph_side]
  apply PolygonCell.ext
  change
    (Circle.exp
      (2 * Real.pi /
          ((expand P a).boundary (faceEquiv P a f)).length *
        (((faceWeights P a f).take i).sum +
          (faceWeights P a f).get
              (Fin.cast (faceWeights_length P a f).symm i) *
            (t : ℝ))) : ℂ) =
      (Circle.exp
        (PolygonCell.sideAngle (expandedStartIndex P a f i)
          (firstHalfParameter t ht)) : ℂ)
  rw [faceWeights_get,
    (dartWeight_eq_two_iff a _).2 hselected]
  unfold PolygonCell.sideAngle
  rw [expandedStartIndex_val, firstHalfParameter_val]
  push_cast
  ring

/--
@isnad1 id=eq.3h5v.s10.abb117617066 from=translated src=- shape=2893cfa6 vocab=5f108060
-/
theorem faceHomeomorph_side_secondHalf
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hselected : edgeOfDart ((P.boundary f).get i) = a)
    (t : unitInterval) (ht : 1 / 2 ≤ (t : ℝ)) :
    faceHomeomorph P a validP f (PolygonCell.side i t) =
      PolygonCell.side (secondExpandedIndex P a f i hselected)
        (secondHalfParameter t ht) := by
  rw [faceHomeomorph_side]
  apply PolygonCell.ext
  change
    (Circle.exp
      (2 * Real.pi /
          ((expand P a).boundary (faceEquiv P a f)).length *
        (((faceWeights P a f).take i).sum +
          (faceWeights P a f).get
              (Fin.cast (faceWeights_length P a f).symm i) *
            (t : ℝ))) : ℂ) =
      (Circle.exp
        (PolygonCell.sideAngle
          (secondExpandedIndex P a f i hselected)
          (secondHalfParameter t ht)) : ℂ)
  rw [faceWeights_get,
    (dartWeight_eq_two_iff a _).2 hselected]
  unfold PolygonCell.sideAngle
  rw [secondExpandedIndex_val, secondHalfParameter_val]
  push_cast
  ring

/--
@isnad1 id=eq.2h4v.s8.0990ef7a120c from=translated src=- shape=2b299d6a vocab=e5dc70b7
-/
theorem preHomeomorph_occurrenceSide_of_not_selected
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (o : P.BoundaryOccurrence)
    (hnot : o.edge ≠ a) (t : unitInterval) :
    preHomeomorph P a validP ((P.occurrenceSide o).point t) =
      ((expand P a).occurrenceSide
        (expandedOccurrenceAt P a ⟨o, zeroOffset a o.dart⟩)).point t := by
  rcases o with ⟨f, i⟩
  change
    (⟨faceEquiv P a f,
        faceHomeomorph P a validP f (PolygonCell.side i t)⟩ :
      (expand P a).PolygonalPreRealization) =
      ⟨faceEquiv P a f,
        PolygonCell.side
          (expandedOffsetIndex P a f i
            (zeroOffset a ((P.boundary f).get i))) t⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    rw [faceHomeomorph_side_of_not_selected P a validP f i hnot]
    congr 2

/--
@isnad1 id=eq.3h4v.s8.c060d8d393cb from=translated src=- shape=f4aa72c2 vocab=e4aaf676
-/
theorem preHomeomorph_occurrenceSide_firstHalf
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (o : P.BoundaryOccurrence)
    (hselected : o.edge = a) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    preHomeomorph P a validP ((P.occurrenceSide o).point t) =
      ((expand P a).occurrenceSide
        (expandedOccurrenceAt P a
          ⟨o, zeroOffset a o.dart⟩)).point
        (firstHalfParameter t ht) := by
  rcases o with ⟨f, i⟩
  change
    (⟨faceEquiv P a f,
        faceHomeomorph P a validP f (PolygonCell.side i t)⟩ :
      (expand P a).PolygonalPreRealization) =
      ⟨faceEquiv P a f,
        PolygonCell.side
          (expandedOffsetIndex P a f i
            (zeroOffset a ((P.boundary f).get i)))
          (firstHalfParameter t ht)⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    rw [faceHomeomorph_side_firstHalf P a validP f i hselected t ht]
    congr 2

/--
@isnad1 id=eq.3h4v.s8.a0b1152ecc98 from=translated src=- shape=04fdea8b vocab=f93e43f7
-/
theorem preHomeomorph_occurrenceSide_secondHalf
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (o : P.BoundaryOccurrence)
    (hselected : o.edge = a) (t : unitInterval)
    (ht : 1 / 2 ≤ (t : ℝ)) :
    preHomeomorph P a validP ((P.occurrenceSide o).point t) =
      ((expand P a).occurrenceSide
        (expandedOccurrenceAt P a
          ⟨o, oneOffset a o.dart hselected⟩)).point
        (secondHalfParameter t ht) := by
  rcases o with ⟨f, i⟩
  have hselected' :
      edgeOfDart ((P.boundary f).get i) = a :=
    hselected
  change
    (⟨faceEquiv P a f,
        faceHomeomorph P a validP f (PolygonCell.side i t)⟩ :
      (expand P a).PolygonalPreRealization) =
      ⟨faceEquiv P a f,
        PolygonCell.side
          (expandedOffsetIndex P a f i
            (oneOffset a ((P.boundary f).get i) hselected'))
          (secondHalfParameter t ht)⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    rw [faceHomeomorph_side_secondHalf P a validP f i hselected t ht]
    congr 2

/--
@isnad1 id=eq.1h4v.s5.55e07e8dd6dc from=translated src=- shape=febed6ac vocab=179026a0
-/
@[simp]
theorem samePairedOffset_val
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) :
    (samePairedOffset a pairing hcompatible k).val = k.val :=
  rfl

/--
@isnad1 id=eq.1h4v.s6.9e7e004ba7d4 from=translated src=- shape=8696f743 vocab=0a2e60c8
-/
@[simp]
theorem oppositePairedOffset_val
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) :
    (oppositePairedOffset a pairing hcompatible k).val =
      dartWeight a pairing.source.dart - (k.val + 1) := by
  rfl

/--
@isnad1 id=eq.1h1v.s5.a2a78f289482 from=translated src=- shape=ee980c82 vocab=6ddd9477
-/
theorem symm_firstHalfParameter
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    unitInterval.symm (firstHalfParameter t ht) =
      secondHalfParameter (unitInterval.symm t) (by
        change 1 / 2 ≤ 1 - (t : ℝ)
        linarith) := by
  apply Subtype.ext
  simp [firstHalfParameter, secondHalfParameter, unitInterval.symm]
  ring

/--
@isnad1 id=eq.1h1v.s5.d88030b76b58 from=translated src=- shape=bef52735 vocab=a33ab041
-/
theorem symm_secondHalfParameter
    (t : unitInterval) (ht : 1 / 2 ≤ (t : ℝ)) :
    unitInterval.symm (secondHalfParameter t ht) =
      firstHalfParameter (unitInterval.symm t) (by
        change 1 - (t : ℝ) ≤ 1 / 2
        linarith) := by
  apply Subtype.ext
  simp [firstHalfParameter, secondHalfParameter, unitInterval.symm]
  ring

/--
@isnad1 id=r.2h5v.s7.67ed273941d0 from=translated src=- shape=50cf52ad vocab=6ee82271
-/
theorem expandedPairingSame_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validQ : (expand P a).IsSurfaceValid)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart))
    (u : unitInterval) :
    (expand P a).PolygonalGluingRel validQ
      (((expand P a).occurrenceSide
        (expandedOccurrenceAt P a ⟨pairing.source, k⟩)).point u)
      (((expand P a).occurrenceSide
        (expandedOccurrenceAt P a
          ⟨pairing.target,
            samePairedOffset a pairing hcompatible k⟩)).point u) := by
  exact PolygonGluing.related_of_mem
    (expandedPairingSame P a pairing hcompatible k).identification
    (pairing_identification_mem validQ
      (expandedPairingSame P a pairing hcompatible k)) u

/--
@isnad1 id=r.2h5v.s7.8a3d212b4732 from=translated src=- shape=6b050b4a vocab=bb7cf8de
-/
theorem expandedPairingOpposite_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validQ : (expand P a).IsSurfaceValid)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart))
    (u : unitInterval) :
    (expand P a).PolygonalGluingRel validQ
      (((expand P a).occurrenceSide
        (expandedOccurrenceAt P a ⟨pairing.source, k⟩)).point u)
      (((expand P a).occurrenceSide
        (expandedOccurrenceAt P a
          ⟨pairing.target,
            oppositePairedOffset a pairing hcompatible k⟩)).point
        (unitInterval.symm u)) := by
  exact PolygonGluing.related_of_mem
    (expandedPairingOpposite P a pairing hcompatible k).identification
    (pairing_identification_mem validQ
      (expandedPairingOpposite P a pairing hcompatible k)) u

/-- The facewise P1 map sends every source gluing generator into the target generated
relation.
@isnad1 id=r.1h4v.s9.2176106e6946 from=translated src=- shape=05893aff vocab=7a6bba1f
-/
theorem preHomeomorph_generator_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (t : unitInterval) :
    (expand P a).PolygonalGluingRel (expand_isSurfaceValid P a validP)
      (preHomeomorph P a validP
        (pairing.identification.source.point t))
      (preHomeomorph P a validP
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  let validQ := expand_isSurfaceValid P a validP
  change
    (expand P a).PolygonalGluingRel validQ
      (preHomeomorph P a validP
        ((P.occurrenceSide pairing.source).point t))
      (preHomeomorph P a validP
        ((P.occurrenceSide pairing.target).point
          (pairing.identification.parameter t)))
  have hedge : pairing.target.edge = pairing.source.edge :=
    BoundaryPairing.target_edge_eq_source_edge pairing
  cases hdirection : pairing.direction with
  | same =>
      have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      have hparameter :
          pairing.identification.parameter t = t := by
        simp [BoundaryPairing.identification, PolygonGluing.Identification.parameter,
          hdirection]
      rw [hparameter]
      by_cases hselected : pairing.source.edge = a
      · have htargetSelected : pairing.target.edge = a :=
          hedge.trans hselected
        by_cases ht : (t : ℝ) ≤ 1 / 2
        · rw [preHomeomorph_occurrenceSide_firstHalf
              P a validP pairing.source hselected t ht,
            preHomeomorph_occurrenceSide_firstHalf
              P a validP pairing.target htargetSelected t ht]
          have hoffset :
              samePairedOffset a pairing hcompatible
                  (zeroOffset a pairing.source.dart) =
                zeroOffset a pairing.target.dart := by
            apply Fin.ext
            rfl
          rw [← hoffset]
          exact expandedPairingSame_related P a validQ pairing hcompatible
            (zeroOffset a pairing.source.dart) (firstHalfParameter t ht)
        · have ht' : 1 / 2 ≤ (t : ℝ) := le_of_not_ge ht
          rw [preHomeomorph_occurrenceSide_secondHalf
              P a validP pairing.source hselected t ht',
            preHomeomorph_occurrenceSide_secondHalf
              P a validP pairing.target htargetSelected t ht']
          have hoffset :
              samePairedOffset a pairing hcompatible
                  (oneOffset a pairing.source.dart hselected) =
                oneOffset a pairing.target.dart htargetSelected := by
            apply Fin.ext
            rfl
          rw [← hoffset]
          exact expandedPairingSame_related P a validQ pairing hcompatible
            (oneOffset a pairing.source.dart hselected)
            (secondHalfParameter t ht')
      · have htargetNot : pairing.target.edge ≠ a := by
          rw [hedge]
          exact hselected
        rw [preHomeomorph_occurrenceSide_of_not_selected
              P a validP pairing.source hselected t,
            preHomeomorph_occurrenceSide_of_not_selected
              P a validP pairing.target htargetNot t]
        have hoffset :
            samePairedOffset a pairing hcompatible
                (zeroOffset a pairing.source.dart) =
              zeroOffset a pairing.target.dart := by
          apply Fin.ext
          rfl
        rw [← hoffset]
        exact expandedPairingSame_related P a validQ pairing hcompatible
          (zeroOffset a pairing.source.dart) t
  | opposite =>
      have hcompatible :
          pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      have hparameter :
          pairing.identification.parameter t = unitInterval.symm t := by
        simp [BoundaryPairing.identification, PolygonGluing.Identification.parameter,
          hdirection, PolygonGluing.ParameterDirection.homeomorph_opposite_apply]
      rw [hparameter]
      by_cases hselected : pairing.source.edge = a
      · have htargetSelected : pairing.target.edge = a :=
          hedge.trans hselected
        by_cases ht : (t : ℝ) ≤ 1 / 2
        · have hsymmHalf :
              1 / 2 ≤ (unitInterval.symm t : ℝ) := by
            change 1 / 2 ≤ 1 - (t : ℝ)
            linarith
          rw [preHomeomorph_occurrenceSide_firstHalf
              P a validP pairing.source hselected t ht,
            preHomeomorph_occurrenceSide_secondHalf
              P a validP pairing.target htargetSelected
                (unitInterval.symm t) hsymmHalf]
          have hoffset :
              oppositePairedOffset a pairing hcompatible
                  (zeroOffset a pairing.source.dart) =
                oneOffset a pairing.target.dart htargetSelected := by
            apply Fin.ext
            have hw :
                dartWeight a pairing.source.dart = 2 :=
              (dartWeight_eq_two_iff a _).2 hselected
            simp [oppositePairedOffset_val, hw, zeroOffset, oneOffset]
          rw [← hoffset, ← symm_firstHalfParameter t ht]
          exact expandedPairingOpposite_related P a validQ pairing hcompatible
            (zeroOffset a pairing.source.dart) (firstHalfParameter t ht)
        · have ht' : 1 / 2 ≤ (t : ℝ) := le_of_not_ge ht
          have hsymmHalf :
              (unitInterval.symm t : ℝ) ≤ 1 / 2 := by
            change 1 - (t : ℝ) ≤ 1 / 2
            linarith
          rw [preHomeomorph_occurrenceSide_secondHalf
              P a validP pairing.source hselected t ht',
            preHomeomorph_occurrenceSide_firstHalf
              P a validP pairing.target htargetSelected
                (unitInterval.symm t) hsymmHalf]
          have hoffset :
              oppositePairedOffset a pairing hcompatible
                  (oneOffset a pairing.source.dart hselected) =
                zeroOffset a pairing.target.dart := by
            apply Fin.ext
            have hw :
                dartWeight a pairing.source.dart = 2 :=
              (dartWeight_eq_two_iff a _).2 hselected
            simp [oppositePairedOffset_val, hw, zeroOffset, oneOffset]
          rw [← hoffset, ← symm_secondHalfParameter t ht']
          exact expandedPairingOpposite_related P a validQ pairing hcompatible
            (oneOffset a pairing.source.dart hselected)
            (secondHalfParameter t ht')
      · have htargetNot : pairing.target.edge ≠ a := by
          rw [hedge]
          exact hselected
        rw [preHomeomorph_occurrenceSide_of_not_selected
              P a validP pairing.source hselected t,
            preHomeomorph_occurrenceSide_of_not_selected
              P a validP pairing.target htargetNot (unitInterval.symm t)]
        have hoffset :
            oppositePairedOffset a pairing hcompatible
                (zeroOffset a pairing.source.dart) =
              zeroOffset a pairing.target.dart := by
          apply Fin.ext
          have hw :
              dartWeight a pairing.source.dart = 1 :=
            (dartWeight_eq_one_iff a _).2 hselected
          simp [oppositePairedOffset_val, hw, zeroOffset]
        rw [← hoffset]
        exact expandedPairingOpposite_related P a validQ pairing hcompatible
          (zeroOffset a pairing.source.dart) t

/--
@isnad1 id=eq.0h2v.s6.74eb8a918729 from=translated src=- shape=93e811af vocab=cf3b2541
-/
theorem card_expandedSourcePosition
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    Fintype.card (ExpandedSourcePosition P a) =
      Fintype.card (expand P a).BoundaryOccurrence := by
  simp only [ExpandedSourcePosition, BoundaryOccurrence,
    Fintype.card_sigma, Fintype.card_fin]
  rw [Fintype.sum_sigma]
  calc
    (∑ f : P.Face,
        ∑ i : Fin (P.boundary f).length,
          dartWeight a ((P.boundary f).get i)) =
        ∑ f : P.Face, (faceWeights P a f).sum := by
      apply Finset.sum_congr rfl
      intro f _hf
      rw [← List.sum_ofFn]
      congr 1
      ext i
      simp [faceWeights]
    _ = ∑ q : (expand P a).Face,
          ((expand P a).boundary q).length := by
      apply Fintype.sum_equiv (faceEquiv P a)
      intro f
      exact faceWeights_sum P a f

/-- Expanded source blocks enumerate all target boundary occurrences. -/
noncomputable def expandedOccurrenceEquiv
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    ExpandedSourcePosition P a ≃ (expand P a).BoundaryOccurrence :=
  Equiv.ofBijective (expandedOccurrenceAt P a)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨expandedOccurrenceAt_injective P a,
        card_expandedSourcePosition P a⟩)

/--
@isnad1 id=eq.0h3v.s6.0a9565adbd67 from=translated src=- shape=3de24bf5 vocab=39c3a1e7
-/
@[simp]
theorem expandedOccurrenceEquiv_apply
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    expandedOccurrenceEquiv P a p = expandedOccurrenceAt P a p :=
  rfl

/-- Contract either target subedge back to its source edge. -/
def contractExpandedEdge {n : ℕ} (a : Fin n) : Fin (n + 1) → Fin n :=
  Fin.lastCases a id

/--
@isnad1 id=eq.0h3v.s4.9fac11746744 from=translated src=- shape=dd90247e vocab=0ef50c14
-/
@[simp]
theorem contractExpandedEdge_castSucc {n : ℕ} (a e : Fin n) :
    contractExpandedEdge a e.castSucc = e := by
  simp [contractExpandedEdge]

/--
@isnad1 id=eq.0h2v.s3.49e35b908af0 from=translated src=- shape=ce413fbc vocab=45bc4453
-/
@[simp]
theorem contractExpandedEdge_freshEdge {n : ℕ} (a : Fin n) :
    contractExpandedEdge a (freshEdge n) = a := by
  simp [contractExpandedEdge, freshEdge]

/--
@isnad1 id=eq.0h4v.s4.4a182544866b from=translated src=- shape=cefe9d3b vocab=9e5f241e
-/
theorem contractExpandedEdge_expandedSubedge {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) (k : Fin (dartWeight a d)) :
    contractExpandedEdge a (expandedSubedge a d k) = edgeOfDart d := by
  cases d with
  | pos e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        interval_cases hkval : k.val <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart, hkval, firstSubedge]
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
          he, hk0]
  | neg e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        interval_cases hkval : k.val <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart, hkval, firstSubedge]
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
          he, hk0]

/--
@isnad1 id=eq.1h6v.s5.598c179ae5f0 from=translated src=- shape=65c3506f vocab=0379e365
-/
theorem sourceEdge_eq_of_expandedSubedge_eq {n : ℕ} (a : Fin n)
    {d e : SignedDart (Fin n)}
    {k : Fin (dartWeight a d)} {l : Fin (dartWeight a e)}
    (h : expandedSubedge a d k = expandedSubedge a e l) :
    edgeOfDart d = edgeOfDart e := by
  have := congrArg (contractExpandedEdge a) h
  simpa only [contractExpandedEdge_expandedSubedge] using this

/--
@isnad1 id=injectiv.0h3v.s5.bf0b21256040 from=translated src=- shape=70871beb vocab=8cc3d0bf
-/
theorem expandedSubedge_injective_offset {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    Function.Injective (expandedSubedge a d) := by
  intro k l h
  cases d with
  | pos e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        have hl : l.val < 2 := by
          simpa [dartWeight, edgeOfDart] using l.isLt
        apply Fin.ext
        interval_cases hkval : k.val <;>
          interval_cases hlval : l.val <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            hkval, hlval,
            firstSubedge_ne_freshEdge,
            (firstSubedge_ne_freshEdge a).symm] at h ⊢
      · apply Fin.ext
        have hk : k.val < 1 := by
          simpa [dartWeight, edgeOfDart, he] using k.isLt
        have hl : l.val < 1 := by
          simpa [dartWeight, edgeOfDart, he] using l.isLt
        omega
  | neg e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        have hl : l.val < 2 := by
          simpa [dartWeight, edgeOfDart] using l.isLt
        apply Fin.ext
        interval_cases hkval : k.val <;>
          interval_cases hlval : l.val <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            hkval, hlval,
            firstSubedge_ne_freshEdge,
            (firstSubedge_ne_freshEdge a).symm] at h ⊢
      · apply Fin.ext
        have hk : k.val < 1 := by
          simpa [dartWeight, edgeOfDart, he] using k.isLt
        have hl : l.val < 1 := by
          simpa [dartWeight, edgeOfDart, he] using l.isLt
        omega

/--
@isnad1 id=eq.0h3v.s5.bd2ee2b4c3a0 from=translated src=- shape=75f6f9a1 vocab=8965bb5b
-/
theorem expandedOccurrenceAt_edge
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    (expandedOccurrenceAt P a p).edge =
      expandedSubedge a p.1.dart p.2 := by
  rw [BoundaryOccurrence.edge, expandedOccurrenceAt_dart]
  rfl

/--
@isnad1 id=eq.2h4v.s7.2c29586de995 from=translated src=- shape=2d4c6450 vocab=b6c7bbf5
-/
theorem expandedSourcePosition_eq_of_fst_eq_of_subedge_eq
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p q : ExpandedSourcePosition P a)
    (hfst : p.1 = q.1)
    (hedge :
      expandedSubedge a p.1.dart p.2 =
        expandedSubedge a q.1.dart q.2) :
    p = q := by
  rcases p with ⟨o, k⟩
  rcases q with ⟨o', l⟩
  cases hfst
  have hkl : k = l :=
    expandedSubedge_injective_offset a o.dart hedge
  subst l
  rfl

/--
@isnad1 id=eq.1h5v.s6.fd5f66aa57e7 from=translated src=- shape=d4025500 vocab=9ddf8e5a
-/
theorem expandedSourcePosition_mk_transport
    (P : FiniteCyclicPresentation) (a : P.Edge)
    {o o' : P.BoundaryOccurrence} (h : o = o')
    (k : Fin (dartWeight a o'.dart)) :
    (⟨o, h.symm ▸ k⟩ : ExpandedSourcePosition P a) = ⟨o', k⟩ := by
  cases h
  rfl

/--
@isnad1 id=eq.2h3v.s5.8dbf6668babd from=translated src=- shape=3b88bb8c vocab=1aa2c067
-/
theorem BoundaryPairing.direction_eq_of_source_target_eq
    {P : FiniteCyclicPresentation} (p q : P.BoundaryPairing)
    (hsource : p.source = q.source) (htarget : p.target = q.target) :
    p.direction = q.direction := by
  have hsourceDart := congrArg BoundaryOccurrence.dart hsource
  have htargetDart := congrArg BoundaryOccurrence.dart htarget
  cases hp : p.direction <;> cases hq : q.direction
  · rfl
  · have hpcompat : p.target.dart = p.source.dart := by
      simpa only [hp] using p.compatible
    have hqcompat : q.target.dart = q.source.dart.flip := by
      simpa only [hq] using q.compatible
    have hbad : p.source.dart = p.source.dart.flip := by
      calc
        p.source.dart = p.target.dart := hpcompat.symm
        _ = q.target.dart := htargetDart
        _ = q.source.dart.flip := hqcompat
        _ = p.source.dart.flip := congrArg SignedDart.flip hsourceDart.symm
    cases hdart : p.source.dart <;>
      simp [hdart, SignedDart.flip] at hbad
  · have hpcompat : p.target.dart = p.source.dart.flip := by
      simpa only [hp] using p.compatible
    have hqcompat : q.target.dart = q.source.dart := by
      simpa only [hq] using q.compatible
    have hbad : p.source.dart.flip = p.source.dart := by
      calc
        p.source.dart.flip = p.target.dart := hpcompat.symm
        _ = q.target.dart := htargetDart
        _ = q.source.dart := hqcompat
        _ = p.source.dart := hsourceDart.symm
    cases hdart : p.source.dart <;>
      simp [hdart, SignedDart.flip] at hbad
  · rfl

theorem BoundaryPairing.eq_of_source_target_direction_eq
    {P : FiniteCyclicPresentation} (p q : P.BoundaryPairing)
    (hsource : p.source = q.source) (htarget : p.target = q.target)
    (hdirection : p.direction = q.direction) :
    p = q := by
  cases p
  cases q
  simp_all

/-- Every target pairing is one of the subedge pairings expanded from a unique old pairing.
@isnad1 id=or.1h3v.s7.112c567bc38a from=translated src=- shape=32259e51 vocab=e7f5bce3
-/
theorem exists_eq_expandedPairing
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid)
    (q : (expand P a).BoundaryPairing) :
    (∃ (r : P.BoundaryPairing)
        (_hdirection : r.direction = .same)
        (hcompatible : r.target.dart = r.source.dart)
        (k : Fin (dartWeight a r.source.dart)),
        q = expandedPairingSame P a r hcompatible k) ∨
      (∃ (r : P.BoundaryPairing)
        (_hdirection : r.direction = .opposite)
        (hcompatible : r.target.dart = r.source.dart.flip)
        (k : Fin (dartWeight a r.source.dart)),
        q = expandedPairingOpposite P a r hcompatible k) := by
  let e := expandedOccurrenceEquiv P a
  let ps : ExpandedSourcePosition P a := e.symm q.source
  let pt : ExpandedSourcePosition P a := e.symm q.target
  have hps : expandedOccurrenceAt P a ps = q.source :=
    e.apply_symm_apply q.source
  have hpt : expandedOccurrenceAt P a pt = q.target :=
    e.apply_symm_apply q.target
  have hqedge : q.target.edge = q.source.edge :=
    BoundaryPairing.target_edge_eq_source_edge q
  have hsubedge :
      expandedSubedge a ps.1.dart ps.2 =
        expandedSubedge a pt.1.dart pt.2 := by
    have hqedge' := hqedge
    rw [← hpt, ← hps, expandedOccurrenceAt_edge,
      expandedOccurrenceAt_edge] at hqedge'
    exact hqedge'.symm
  have holdEdge : ps.1.edge = pt.1.edge :=
    sourceEdge_eq_of_expandedSubedge_eq a hsubedge
  have holdNe : ps.1 ≠ pt.1 := by
    intro heq
    have hpEq :=
      expandedSourcePosition_eq_of_fst_eq_of_subedge_eq
        P a ps pt heq hsubedge
    apply q.source_ne_target
    calc
      q.source = expandedOccurrenceAt P a ps := hps.symm
      _ = expandedOccurrenceAt P a pt :=
        congrArg (expandedOccurrenceAt P a) hpEq
      _ = q.target := hpt
  have hsourceInternal : ¬P.IsBoundaryEdge ps.1.edge := by
    intro hb
    apply q.source_not_boundary
    rw [← hps, expandedOccurrenceAt_edge]
    exact
      (isBoundaryEdge_expandedSubedge_iff
        P a ps.1.dart ps.2).2 hb
  obtain ⟨r, hrsource⟩ :=
    validP.exists_pairing_source ps.1 hsourceInternal
  obtain ⟨partner, _hpartner, hunique⟩ :=
    validP.exists_unique_partner ps.1 hsourceInternal
  have hrcondition :
      ps.1 ≠ r.target ∧ r.target.edge = ps.1.edge := by
    constructor
    · intro heq
      apply r.source_ne_target
      rw [hrsource, heq]
    · rw [← hrsource]
      exact BoundaryPairing.target_edge_eq_source_edge r
  have htcondition :
      ps.1 ≠ pt.1 ∧ pt.1.edge = ps.1.edge :=
    ⟨holdNe, holdEdge.symm⟩
  have hrtarget : r.target = pt.1 :=
    (hunique r.target hrcondition).trans
      (hunique pt.1 htcondition).symm
  let k : Fin (dartWeight a r.source.dart) :=
    hrsource.symm ▸ ps.2
  have hposition :
      (⟨r.source, k⟩ : ExpandedSourcePosition P a) = ps := by
    change
      (⟨r.source, hrsource.symm ▸ ps.2⟩ :
        ExpandedSourcePosition P a) = ps
    exact (expandedSourcePosition_mk_transport P a hrsource ps.2).trans
      (Sigma.eta ps)
  let validQ := expand_isSurfaceValid P a validP
  cases hdirection : r.direction with
  | same =>
      have hcompatible : r.target.dart = r.source.dart := by
        simpa only [hdirection] using r.compatible
      let er := expandedPairingSame P a r hcompatible k
      have hersource : er.source = q.source := by
        change
          expandedOccurrenceAt P a ⟨r.source, k⟩ = q.source
        rw [hposition, hps]
      obtain ⟨qpartner, _hqpartner, hqunique⟩ :=
        validQ.exists_unique_partner q.source q.source_not_boundary
      have hercondition :
          q.source ≠ er.target ∧ er.target.edge = q.source.edge := by
        constructor
        · intro heq
          apply er.source_ne_target
          exact hersource.trans heq
        · calc
            er.target.edge = er.source.edge :=
              BoundaryPairing.target_edge_eq_source_edge er
            _ = q.source.edge :=
              congrArg BoundaryOccurrence.edge hersource
      have hqcondition :
          q.source ≠ q.target ∧ q.target.edge = q.source.edge :=
        ⟨q.source_ne_target, hqedge⟩
      have hertarget : er.target = q.target :=
        (hqunique er.target hercondition).trans
          (hqunique q.target hqcondition).symm
      have hdirectionEq : q.direction = er.direction :=
        BoundaryPairing.direction_eq_of_source_target_eq q er
          hersource.symm hertarget.symm
      exact Or.inl
        ⟨r, hdirection, hcompatible, k,
          BoundaryPairing.eq_of_source_target_direction_eq q er
            hersource.symm hertarget.symm hdirectionEq⟩
  | opposite =>
      have hcompatible : r.target.dart = r.source.dart.flip := by
        simpa only [hdirection] using r.compatible
      let er := expandedPairingOpposite P a r hcompatible k
      have hersource : er.source = q.source := by
        change
          expandedOccurrenceAt P a ⟨r.source, k⟩ = q.source
        rw [hposition, hps]
      obtain ⟨qpartner, _hqpartner, hqunique⟩ :=
        validQ.exists_unique_partner q.source q.source_not_boundary
      have hercondition :
          q.source ≠ er.target ∧ er.target.edge = q.source.edge := by
        constructor
        · intro heq
          apply er.source_ne_target
          exact hersource.trans heq
        · calc
            er.target.edge = er.source.edge :=
              BoundaryPairing.target_edge_eq_source_edge er
            _ = q.source.edge :=
              congrArg BoundaryOccurrence.edge hersource
      have hqcondition :
          q.source ≠ q.target ∧ q.target.edge = q.source.edge :=
        ⟨q.source_ne_target, hqedge⟩
      have hertarget : er.target = q.target :=
        (hqunique er.target hercondition).trans
          (hqunique q.target hqcondition).symm
      have hdirectionEq : q.direction = er.direction :=
        BoundaryPairing.direction_eq_of_source_target_eq q er
          hersource.symm hertarget.symm
      exact Or.inr
        ⟨r, hdirection, hcompatible, k,
          BoundaryPairing.eq_of_source_target_direction_eq q er
            hersource.symm hertarget.symm hdirectionEq⟩

/--
@isnad1 id=lt.0h3v.s4.a8444e410e6b from=translated src=- shape=931faef3 vocab=281bcc77
-/
theorem dartWeight_pos {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    0 < dartWeight a d := by
  unfold dartWeight
  split <;> omega

/-- Convert a target subedge-local parameter back to the original source-side parameter. -/
noncomputable def unexpandParameter {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (k : Fin (dartWeight a d)) (u : unitInterval) : unitInterval :=
  ⟨((k : ℝ) + (u : ℝ)) / dartWeight a d,
    div_nonneg (add_nonneg (Nat.cast_nonneg _) u.property.1)
      (Nat.cast_nonneg _), by
    rw [div_le_one (by exact_mod_cast dartWeight_pos a d)]
    have hk : (k.val : ℝ) + 1 ≤ dartWeight a d := by
      exact_mod_cast k.isLt
    linarith [u.property.2]⟩

/--
@isnad1 id=eq.0h5v.s6.08bed2a7d7cf from=translated src=- shape=ad459384 vocab=039f1639
-/
@[simp]
theorem unexpandParameter_val {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) (k : Fin (dartWeight a d))
    (u : unitInterval) :
    (unexpandParameter a d k u : ℝ) =
      ((k : ℝ) + (u : ℝ)) / dartWeight a d :=
  rfl

/--
@isnad1 id=eq.1h6v.s10.eef6aed7eb49 from=translated src=- shape=2fe076f1 vocab=86f1c67e
-/
theorem faceHomeomorph_side_unexpand
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (k : Fin (dartWeight a ((P.boundary f).get i)))
    (u : unitInterval) :
    faceHomeomorph P a validP f
        (PolygonCell.side i
          (unexpandParameter a ((P.boundary f).get i) k u)) =
      PolygonCell.side (expandedOffsetIndex P a f i k) u := by
  rw [faceHomeomorph_side]
  change
    PolygonCell.ofCircle
        ((expand P a).boundary (faceEquiv P a f)).length
        (Circle.exp
          (2 * Real.pi /
              ((expand P a).boundary (faceEquiv P a f)).length *
            (((faceWeights P a f).take i).sum +
              (faceWeights P a f).get
                  (Fin.cast (faceWeights_length P a f).symm i) *
                (unexpandParameter a ((P.boundary f).get i) k u : ℝ)))) =
      PolygonCell.ofCircle
        ((expand P a).boundary (faceEquiv P a f)).length
        (Circle.exp
          (PolygonCell.sideAngle (expandedOffsetIndex P a f i k) u))
  apply congrArg
    (PolygonCell.ofCircle
      ((expand P a).boundary (faceEquiv P a f)).length)
  apply congrArg Circle.exp
  rw [faceWeights_get]
  unfold PolygonCell.sideAngle
  rw [expandedOffsetIndex_val, unexpandParameter_val]
  have hw : (dartWeight a ((P.boundary f).get i) : ℝ) ≠ 0 := by
    exact_mod_cast (dartWeight_pos a ((P.boundary f).get i)).ne'
  push_cast
  field_simp [hw]
  ring

/--
@isnad1 id=eq.1h4v.s8.2843a90fb39d from=translated src=- shape=073c43e6 vocab=1d5795a7
-/
theorem preHomeomorph_occurrenceSide_unexpand
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (p : ExpandedSourcePosition P a)
    (u : unitInterval) :
    preHomeomorph P a validP
        ((P.occurrenceSide p.1).point
          (unexpandParameter a p.1.dart p.2 u)) =
      ((expand P a).occurrenceSide
        (expandedOccurrenceAt P a p)).point u := by
  rcases p with ⟨⟨f, i⟩, k⟩
  change
    (⟨faceEquiv P a f,
        faceHomeomorph P a validP f
          (PolygonCell.side i
            (unexpandParameter a ((P.boundary f).get i) k u))⟩ :
      (expand P a).PolygonalPreRealization) =
      ⟨faceEquiv P a f,
        PolygonCell.side (expandedOffsetIndex P a f i k) u⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    exact faceHomeomorph_side_unexpand P a validP f i k u

/--
@isnad1 id=eq.1h4v.s8.3baa018daec5 from=translated src=- shape=9acdf3db vocab=8016f58f
-/
theorem preHomeomorph_symm_expandedOccurrenceAt
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (p : ExpandedSourcePosition P a)
    (u : unitInterval) :
    (preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a p)).point u) =
      (P.occurrenceSide p.1).point
        (unexpandParameter a p.1.dart p.2 u) := by
  apply (preHomeomorph P a validP).injective
  rw [(preHomeomorph P a validP).apply_symm_apply]
  exact (preHomeomorph_occurrenceSide_unexpand P a validP p u).symm

/--
@isnad1 id=eq.1h6v.s5.39b7d75c1f95 from=translated src=- shape=e21ce903 vocab=d5456375
-/
theorem unexpandParameter_cast_eq {n : ℕ} (a : Fin n)
    {d₁ d₂ : SignedDart (Fin n)} (h : d₂ = d₁)
    (k : Fin (dartWeight a d₁)) (u : unitInterval) :
    unexpandParameter a d₂
        (Fin.cast (congrArg (dartWeight a) h.symm) k) u =
      unexpandParameter a d₁ k u := by
  subst d₂
  rfl

/--
@isnad1 id=eq.0h5v.s5.27f3eaa7df2d from=translated src=- shape=ec611407 vocab=61e4c5b1
-/
theorem unexpandParameter_flip_reverse {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) (k : Fin (dartWeight a d))
    (u : unitInterval) :
    unexpandParameter a d.flip (reverseOffset a d k)
        (unitInterval.symm u) =
      unitInterval.symm (unexpandParameter a d k u) := by
  apply Subtype.ext
  simp only [unexpandParameter_val,
    reverseOffset, dartWeight_flip, unitInterval.coe_symm_eq]
  have hk : k.val + 1 ≤ dartWeight a d :=
    k.isLt
  have hw : (dartWeight a d : ℝ) ≠ 0 := by
    exact_mod_cast (dartWeight_pos a d).ne'
  rw [Nat.cast_sub hk]
  push_cast
  field_simp [hw]
  ring

/--
@isnad1 id=eq.1h5v.s6.df8af930180d from=translated src=- shape=3033a135 vocab=9d3fde09
-/
theorem unexpandParameter_samePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) (u : unitInterval) :
    unexpandParameter a pairing.target.dart
        (samePairedOffset a pairing hcompatible k) u =
      unexpandParameter a pairing.source.dart k u :=
  unexpandParameter_cast_eq a hcompatible k u

/--
@isnad1 id=eq.1h5v.s6.05e8666a0392 from=translated src=- shape=62a0f955 vocab=76456783
-/
theorem unexpandParameter_oppositePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) (u : unitInterval) :
    unexpandParameter a pairing.target.dart
        (oppositePairedOffset a pairing hcompatible k)
        (unitInterval.symm u) =
      unitInterval.symm
        (unexpandParameter a pairing.source.dart k u) := by
  exact (unexpandParameter_cast_eq a hcompatible
      (reverseOffset a pairing.source.dart k)
      (unitInterval.symm u)).trans
    (unexpandParameter_flip_reverse a pairing.source.dart k u)

/--
@isnad1 id=r.3h5v.s9.89a16bd06030 from=translated src=- shape=8db06c7b vocab=7e997d88
-/
theorem preHomeomorph_symm_expandedPairingSame_generator_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (hdirection : pairing.direction = .same)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart))
    (u : unitInterval) :
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        ((expandedPairingSame P a pairing hcompatible k).identification.source.point u))
      ((preHomeomorph P a validP).symm
        ((expandedPairingSame P a pairing hcompatible k).identification.target.point
          ((expandedPairingSame P a pairing hcompatible k).identification.parameter u))) := by
  change
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a ⟨pairing.source, k⟩)).point u))
      ((preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a
            ⟨pairing.target,
              samePairedOffset a pairing hcompatible k⟩)).point u))
  rw [preHomeomorph_symm_expandedOccurrenceAt,
    preHomeomorph_symm_expandedOccurrenceAt,
    unexpandParameter_samePairedOffset]
  change
    P.PolygonalGluingRel validP
      ((P.occurrenceSide pairing.source).point
        (unexpandParameter a pairing.source.dart k u))
      ((P.occurrenceSide pairing.target).point
        (unexpandParameter a pairing.source.dart k u))
  simpa [BoundaryPairing.identification,
      PolygonGluing.Identification.parameter, hdirection,
      PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
    PolygonGluing.related_of_mem pairing.identification
      (pairing_identification_mem validP pairing)
      (unexpandParameter a pairing.source.dart k u)

/--
@isnad1 id=r.3h5v.s9.12963764d842 from=translated src=- shape=8e9cf343 vocab=c7621476
-/
theorem preHomeomorph_symm_expandedPairingOpposite_generator_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (hdirection : pairing.direction = .opposite)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart))
    (u : unitInterval) :
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        ((expandedPairingOpposite P a pairing hcompatible k).identification.source.point u))
      ((preHomeomorph P a validP).symm
        ((expandedPairingOpposite P a pairing hcompatible k).identification.target.point
          ((expandedPairingOpposite P a pairing hcompatible k).identification.parameter u))) := by
  change
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a ⟨pairing.source, k⟩)).point u))
      ((preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a
            ⟨pairing.target,
              oppositePairedOffset a pairing hcompatible k⟩)).point
          (unitInterval.symm u)))
  rw [preHomeomorph_symm_expandedOccurrenceAt,
    preHomeomorph_symm_expandedOccurrenceAt,
    unexpandParameter_oppositePairedOffset]
  change
    P.PolygonalGluingRel validP
      ((P.occurrenceSide pairing.source).point
        (unexpandParameter a pairing.source.dart k u))
      ((P.occurrenceSide pairing.target).point
        (unitInterval.symm
          (unexpandParameter a pairing.source.dart k u)))
  simpa [BoundaryPairing.identification,
      PolygonGluing.Identification.parameter, hdirection,
      PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
    PolygonGluing.related_of_mem pairing.identification
      (pairing_identification_mem validP pairing)
      (unexpandParameter a pairing.source.dart k u)

/-! ### Descent to the faithful polygonal quotient -/

/-- The inverse facewise map sends every target gluing generator into the source generated
relation.
@isnad1 id=r.1h4v.s9.e3ae0a63bb5d from=translated src=- shape=307607f9 vocab=f5bd9177
-/
theorem preHomeomorph_symm_generator_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (pairing : (expand P a).BoundaryPairing)
    (t : unitInterval) :
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        (pairing.identification.source.point t))
      ((preHomeomorph P a validP).symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rcases exists_eq_expandedPairing P a validP pairing with
      ⟨r, hdirection, hcompatible, k, rfl⟩ |
      ⟨r, hdirection, hcompatible, k, rfl⟩
  · exact preHomeomorph_symm_expandedPairingSame_generator_related
      P a validP r hdirection hcompatible k t
  · exact preHomeomorph_symm_expandedPairingOpposite_generator_related
      P a validP r hdirection hcompatible k t

/-- The facewise P1 homeomorphism preserves the complete source gluing relation.
@isnad1 id=r.2h4v.s9.1db755c867ae from=translated src=- shape=e228b94f vocab=c36da555
-/
theorem preHomeomorph_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    (expand P a).PolygonalGluingRel (expand_isSurfaceValid P a validP)
      (preHomeomorph P a validP x) (preHomeomorph P a validP y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact preHomeomorph_generator_related P a validP pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The inverse facewise P1 homeomorphism preserves the complete target gluing relation.
@isnad1 id=r.2h4v.s9.830bea76c770 from=translated src=- shape=0dcac007 vocab=f56a57cb
-/
theorem preHomeomorph_symm_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid)
    {x y : (expand P a).PolygonalPreRealization}
    (hxy :
      (expand P a).PolygonalGluingRel (expand_isSurfaceValid P a validP) x y) :
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm x)
      ((preHomeomorph P a validP).symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((expand P a).polygonalIdentifications
        (expand_isSurfaceValid P a validP))) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact preHomeomorph_symm_generator_related P a validP pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The selected P1 pre-realization homeomorphism identifies the two generated gluing relations
exactly.
@isnad1 id=iff.1h4v.s9.0987a6830768 from=translated src=- shape=927decc3 vocab=c36da555
-/
theorem preHomeomorph_related_iff
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (x y : P.PolygonalPreRealization) :
    P.PolygonalGluingRel validP x y ↔
      (expand P a).PolygonalGluingRel (expand_isSurfaceValid P a validP)
        (preHomeomorph P a validP x) (preHomeomorph P a validP y) := by
  constructor
  · exact preHomeomorph_related P a validP
  · intro hxy
    simpa only [Homeomorph.symm_apply_apply] using
      preHomeomorph_symm_related P a validP hxy

/-- Canonical P1 expansion preserves the faithful polygonal realization. -/
noncomputable def realizationHomeomorph
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ
      (expand P a).PolygonalRealization (expand_isSurfaceValid P a validP) :=
  PolygonGluing.realizationCongr (preHomeomorph P a validP)
    (preHomeomorph_related_iff P a validP)

/-- Propositional realization-invariance form for the canonical P1 expansion.
@isnad1 id=polygona.1h2v.s3.480a9ee54fdd from=translated src=- shape=b51342f1 vocab=db327ecd
-/
theorem polygonallyEquivalent
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (expand P a) validP
      (expand_isSurfaceValid P a validP) :=
  ⟨realizationHomeomorph P a validP⟩

end P1

/-- Every P1 subdivision, including signed relabeling of the canonical target, preserves the
faithful polygonal realization.
@isnad1 id=preserve.0h0v.s0.a4ad51702e43 from=translated src=- shape=45709ebd vocab=a4ad5170
-/
theorem P1Subdivision.preservesPolygonalRealization :
    P1Subdivision.PreservesPolygonalRealization := by
  intro P Q hPQ validP validQ
  rcases hPQ with ⟨a, ⟨e⟩⟩
  let validExpand := P1.expand_isSurfaceValid P a validP
  exact (P1.polygonallyEquivalent P a validP).trans
    (e.polygonallyEquivalent validExpand validQ)

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
