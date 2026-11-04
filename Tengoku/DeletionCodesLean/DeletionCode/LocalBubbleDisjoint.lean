import Tengoku.DeletionCodesLean.DeletionCode.SingleEditBubbles
import Tengoku.DeletionCodesLean.DeletionCode.EditLocality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms canonical_word` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms localVertex_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms vertices_disjoint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms localVertex_ne_of_trace` (it only prints; the queue checks the axioms of every declaration). -/

/-!
All vertices of two actual local bubbles are disjoint when their source
intervals are disjoint. Each side is realized by its actual canonical edit
inside the common source; the origin-map locality theorem then applies.
The vertex bounds include the initial and terminal vertices of each path.
-/

namespace DeletionCode.LocalBubbleDisjoint

open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization

variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

def pathWord (p : LocalBubble k source target pos orientation) (side : Bool) : List Bool :=
  if side then p.bubble.positiveWord else p.bubble.negativeWord

/-- The negative path is in the source. The positive path is obtained by
the bubble's canonical edit, whose position may differ within the same run
from the originally selected edit position.-/
def canonicalEdit (p : LocalBubble k source target pos orientation) : Bool → Edit
  | false => .unchanged
  | true => match p.bubble.orientation with
    | .deletion => .delete (p.before.length + editOffset k)
    | .insertion => .insert (p.before.length + editOffset k) p.bubble.bit

def localVertex (p : LocalBubble k source target pos orientation) (side : Bool)
    (offset : ℕ) : SupportComponents.Vertex (windowLength k) :=
  SpectrumPath.vertexAt (listLetters (pathWord p side)) (windowLength k) offset

def vertices (p : LocalBubble k source target pos orientation) (side : Bool) :
    Set (SupportComponents.Vertex (windowLength k)) :=
  {v | ∃ offset, offset + (windowLength k - 1) ≤ (pathWord p side).length ∧
    localVertex p side offset = v}

/--
@isnad1 id=le.0h6v.s5.390806e0a215 from=translated src=- shape=e6cb7f0a vocab=47424f26
-/
theorem source_bound (p : LocalBubble k source target pos orientation) :
    p.before.length + p.bubble.negativeWord.length ≤ source.length := by
  have h := congrArg List.length p.source_eq
  simp only [List.length_append] at h
  omega

/--
@isnad1 id=inside.0h7v.s5.dcd3326fe43e from=translated src=- shape=ba7384ca vocab=b2bd1269
-/
theorem canonical_inside (p : LocalBubble k source target pos orientation) (side : Bool) :
    EditLocality.Inside (canonicalEdit p side) p.before.length p.bubble.negativeWord.length := by
  cases side with
  | false => trivial
  | true =>
    have hcut := cut_bounds p.bubble
    cases ho : p.bubble.orientation <;>
      simp only [canonicalEdit, ho, EditLocality.Inside, BubbleWord.negativeWord] <;> omega

/--
@isnad1 id=valid.0h7v.s5.0f3cc36383ea from=translated src=- shape=336aa07c vocab=b8c6fc65
-/
theorem canonical_valid (p : LocalBubble k source target pos orientation) (side : Bool) :
    (canonicalEdit p side).Valid source.length := by
  have hinside := canonical_inside p side
  have hbound := source_bound p
  cases he : canonicalEdit p side <;>
    simp only [he, EditLocality.Inside, Edit.Valid] at hinside ⊢ <;> omega

/--
@isnad1 id=eq.0h7v.s5.5fba73b9bd45 from=translated src=- shape=8c918792 vocab=65f5b23f
-/
theorem canonical_length (p : LocalBubble k source target pos orientation) (side : Bool) :
    (pathWord p side).length = (canonicalEdit p side).outputLength p.bubble.negativeWord.length := by
  cases side with
  | false => rfl
  | true =>
    have hlength := lengths p.bubble
    cases ho : p.bubble.orientation <;>
      simp only [pathWord, ite_true, canonicalEdit, ho,
        BubbleWord.positiveWord, BubbleWord.negativeWord, Edit.outputLength] <;> omega

/-- The whole output word is reconstructed from the canonical edit and
the actual source decomposition. No supplied substring realization is used.
@isnad1 id=eq.0h7v.s6.747ba8c79e80 from=translated src=- shape=efda338b vocab=11203c5c
-/
theorem canonical_word (p : LocalBubble k source target pos orientation) (side : Bool) :
    (canonicalEdit p side).word (listLetters source) =
      listLetters (p.before ++ (pathWord p side ++ p.after)) := by
  have hsource : source = p.before ++ (p.bubble.negativeWord ++ p.after) := by
    simpa only [List.append_assoc] using p.source_eq
  calc
    _ = (canonicalEdit p side).word
        (listLetters (p.before ++ (p.bubble.negativeWord ++ p.after))) :=
      congrArg (fun word : List Bool => (canonicalEdit p side).word (listLetters word)) hsource
    _ = _ := by
      cases side with
      | false => rfl
      | true =>
        cases ho : p.bubble.orientation with
        | deletion =>
          simpa only [pathWord, ite_true, canonicalEdit, ho,
            BubbleWord.negativeWord, BubbleWord.positiveWord, Edit.word] using
            delete_context p.bubble p.before p.after
        | insertion =>
          simpa only [pathWord, ite_true, canonicalEdit, ho,
            BubbleWord.negativeWord, BubbleWord.positiveWord, Edit.word] using
            insert_context p.bubble p.before p.after

/-- Every bounded actual bubble vertex belongs to the corresponding local
output vertex set of the canonical edit in source coordinates.
@isnad1 id=mem.1h8v.s6.c0d030bf910d from=translated src=- shape=9d541159 vocab=4fe4ced7
-/
theorem localVertex_mem (p : LocalBubble k source target pos orientation) (side : Bool)
    (offset : ℕ) (hbound : offset + (windowLength k - 1) ≤ (pathWord p side).length) :
    localVertex p side offset ∈ EditLocality.localVertices (canonicalEdit p side)
      (listLetters source) p.before.length p.bubble.negativeWord.length (windowLength k) := by
  refine ⟨p.before.length + offset, by omega, ?_, ?_⟩
  · have hlength := canonical_length p side
    omega
  · funext i
    change (canonicalEdit p side).word (listLetters source)
      (p.before.length + offset + i.val) = listLetters (pathWord p side) (offset + i.val)
    rw [canonical_word]
    rw [show p.before.length + offset + i.val = p.before.length + (offset + i.val) by omega]
    exact listLetters_middle p.before (pathWord p side) p.after (offset + i.val)
      (by have hi := i.isLt; omega)

/--
@isnad1 id=le.0h7v.s6.53e846972a25 from=translated src=- shape=03ad8d15 vocab=a17933a4
-/
theorem vertices_subset (p : LocalBubble k source target pos orientation) (side : Bool) :
    vertices p side ⊆ EditLocality.localVertices (canonicalEdit p side)
      (listLetters source) p.before.length p.bubble.negativeWord.length (windowLength k) := by
  rintro v ⟨offset, hbound, rfl⟩
  exact localVertex_mem p side offset hbound

/-- Actual cross-bubble vertex disjointness, simultaneously for both path
sides and including endpoints. Only source interval disjointness is supplied.
@isnad1 id=disjoint.3h12v.s7.6daf1e175187 from=translated src=- shape=077590df vocab=a8c5b3da
-/
theorem vertices_disjoint {a b : ℕ} {target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation} (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble k source target₁ a orientation₁)
    (q : LocalBubble k source target₂ b orientation₂)
    (hdis : Disjoint (SingleEditBubbles.LocalBubble.sourceInterval p)
      (SingleEditBubbles.LocalBubble.sourceInterval q)) (side₁ side₂ : Bool) :
    Disjoint (vertices p side₁) (vertices q side₂) := by
  exact (EditLocality.local_vertex_sets_disjoint hk (listLetters source) hx
    (canonicalEdit p side₁) (canonicalEdit q side₂)
    (canonical_valid p side₁) (canonical_valid q side₂)
    p.before.length p.bubble.negativeWord.length q.before.length q.bubble.negativeWord.length
    (canonical_inside p side₁) (canonical_inside q side₂)
    (source_bound p) (source_bound q) hdis).mono
      (vertices_subset p side₁) (vertices_subset q side₂)

/--
@isnad1 id=ne.5h14v.s7.61cc9b81a5f4 from=translated src=- shape=3849c942 vocab=e6cf7e9f
-/
theorem localVertex_ne {a b : ℕ} {target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation} (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble k source target₁ a orientation₁)
    (q : LocalBubble k source target₂ b orientation₂)
    (hdis : Disjoint (SingleEditBubbles.LocalBubble.sourceInterval p)
      (SingleEditBubbles.LocalBubble.sourceInterval q)) (side₁ side₂ : Bool) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ (pathWord p side₁).length)
    (hj : j + (windowLength k - 1) ≤ (pathWord q side₂).length) :
    localVertex p side₁ i ≠ localVertex q side₂ j := by
  intro heq
  exact Set.disjoint_left.mp (vertices_disjoint hk hx p q hdis side₁ side₂)
    ⟨i, hi, rfl⟩ ⟨j, hj, heq.symm⟩

/--
@isnad1 id=disjoint.3h12v.s7.9afaf9e84c68 from=translated src=- shape=fe4ced6d vocab=6786b07f
-/
theorem vertices_disjoint_of_gap {a b : ℕ} {target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation} (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble k source target₁ a orientation₁)
    (q : LocalBubble k source target₂ b orientation₂)
    (hgap : a + 4 * windowLength k ≤ b) (side₁ side₂ : Bool) :
    Disjoint (vertices p side₁) (vertices q side₂) :=
  vertices_disjoint hk hx p q (SingleEditBubbles.source_intervals_disjoint p q hgap) side₁ side₂

/--
@isnad1 id=disjoint.6h12v.s7.e3b2a30238f5 from=translated src=- shape=cce4db87 vocab=716e92de
-/
theorem vertices_disjoint_of_trace {trace : AlignmentTrace.Trace} (hk : 1 ≤ k)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : FiniteConflictGraph.Separated (4 * windowLength k) trace)
    (i j : Fin trace.length) (hi : FiniteConflictGraph.EditIndex trace i)
    (hj : FiniteConflictGraph.EditIndex trace j) (hne : i ≠ j)
    {target₁ target₂ : List Bool} {orientation₁ orientation₂ : Orientation}
    (p : LocalBubble k trace.source target₁ (trace.sourcePosition i.val) orientation₁)
    (q : LocalBubble k trace.source target₂ (trace.sourcePosition j.val) orientation₂)
    (side₁ side₂ : Bool) : Disjoint (vertices p side₁) (vertices q side₂) :=
  vertices_disjoint hk hx p q
    (SingleEditBubbles.source_intervals_disjoint_of_trace hsep i j hi hj hne p q) side₁ side₂

/--
@isnad1 id=ne.8h14v.s7.dc35cbc86df9 from=translated src=- shape=bcd3e8ae vocab=2cc4de04
-/
theorem localVertex_ne_of_trace {trace : AlignmentTrace.Trace} (hk : 1 ≤ k)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : FiniteConflictGraph.Separated (4 * windowLength k) trace)
    (i j : Fin trace.length) (hi : FiniteConflictGraph.EditIndex trace i)
    (hj : FiniteConflictGraph.EditIndex trace j) (hne : i ≠ j)
    {target₁ target₂ : List Bool} {orientation₁ orientation₂ : Orientation}
    (p : LocalBubble k trace.source target₁ (trace.sourcePosition i.val) orientation₁)
    (q : LocalBubble k trace.source target₂ (trace.sourcePosition j.val) orientation₂)
    (side₁ side₂ : Bool) (a b : ℕ)
    (ha : a + (windowLength k - 1) ≤ (pathWord p side₁).length)
    (hb : b + (windowLength k - 1) ≤ (pathWord q side₂).length) :
    localVertex p side₁ a ≠ localVertex q side₂ b :=
  localVertex_ne hk hx p q
    (SingleEditBubbles.source_intervals_disjoint_of_trace hsep i j hi hj hne p q)
    side₁ side₂ a b ha hb

end DeletionCode.LocalBubbleDisjoint
