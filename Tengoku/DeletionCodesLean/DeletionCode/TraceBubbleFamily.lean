import Tengoku.DeletionCodesLean.DeletionCode.TraceEditData
import Tengoku.DeletionCodesLean.DeletionCode.RunBubbleConstruction
import Tengoku.DeletionCodesLean.DeletionCode.TraceSeparation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms position_margins` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_bubbleAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bubbleAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bubbleAt_source` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bubbleAt_target` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms indexedBubbleWords_orientation` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Every actual edit column of a separated trace is assigned a local bubble for
that one edit on the original source. The target and orientation occur in
the type, so the family cannot substitute an unrelated local replacement.
The finite balanced enumeration is inherited from the proved column counts.
-/
namespace DeletionCode.TraceBubbleFamily

open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData

def BubbleAt (trace : Trace) (k : ℕ) (c : EditColumn trace) :=
  LocalBubble k trace.source (oneEditTarget trace c) (position trace c) (orientation trace c)

/-- Matched-column margins place every actual edit sufficiently far inside
the original source for the constructive run and flank extraction.
@isnad1 id=and.1h3v.s6.d795ac95174c from=translated src=- shape=4f88b280 vocab=a8f59741
-/
theorem position_margins (trace : Trace) (k : ℕ)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    4 * windowLength k ≤ position trace c ∧
      position trace c + 4 * windowLength k ≤ trace.source.length :=
  TraceSeparation.sourcePosition_margins hsep c.val c.property

/-- The local bubble is constructed for the actual edit at its actual
source position. No catalogue word or substring presentation is supplied.
@isnad1 id=nonempty.2h3v.s5.c7454b6702e9 from=translated src=- shape=45248664 vocab=a088d801
-/
theorem exists_bubbleAt (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    Nonempty (BubbleAt trace k c) := by
  have hm := position_margins trace k hsep c
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩
  · unfold BubbleAt
    rw [orientation_of_deletion trace c b hc, oneEditTarget_of_deletion trace c b hc]
    exact exists_deletion_bubble trace.source (position trace c) k hx hm.1 hm.2
  · unfold BubbleAt
    rw [orientation_of_insertion trace c b hc, oneEditTarget_of_insertion trace c b hc]
    obtain ⟨p, _⟩ := exists_insertion_bubble trace.source (position trace c) k b hx hm.1 hm.2
    exact ⟨p⟩

noncomputable def bubbleAt (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    BubbleAt trace k c := Classical.choice (exists_bubbleAt trace k hx hsep c)

/--
@isnad1 id=eq.2h3v.s5.f2629767c88e from=translated src=- shape=ad70582a vocab=4675ded1
-/
theorem bubbleAt_orientation (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    (bubbleAt trace k hx hsep c).bubble.orientation = orientation trace c :=
  (bubbleAt trace k hx hsep c).orientation_eq

/--
@isnad1 id=eq.2h3v.s6.35e89f819447 from=translated src=- shape=16fc5374 vocab=978aef84
-/
theorem bubbleAt_source (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    trace.source = (bubbleAt trace k hx hsep c).before ++
      (bubbleAt trace k hx hsep c).bubble.negativeWord ++ (bubbleAt trace k hx hsep c).after :=
  (bubbleAt trace k hx hsep c).source_eq

/--
@isnad1 id=eq.2h3v.s6.a48f5c127870 from=translated src=- shape=d718acf7 vocab=f08eb2b5
-/
theorem bubbleAt_target (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    oneEditTarget trace c = (bubbleAt trace k hx hsep c).before ++
      (bubbleAt trace k hx hsep c).bubble.positiveWord ++ (bubbleAt trace k hx hsep c).after :=
  (bubbleAt trace k hx hsep c).target_eq

/-- Grammar words indexed by the actual trace edit columns.-/
noncomputable def bubbleWords (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) : EditColumn trace → BubbleWord k :=
  fun c => (bubbleAt trace k hx hsep c).bubble

/-- The same constructed bubbles in the derived balanced Fin (2*t) indexing.-/
noncomputable def indexedBubbleWords (trace : Trace) (k t : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) : Fin (2 * t) → BubbleWord k :=
  fun i => bubbleWords trace k hx hsep (editEquiv trace t hdel hins i)

/--
@isnad1 id=eq.4h4v.s7.172596b79295 from=translated src=- shape=a5871549 vocab=8bcb653b
-/
theorem indexedBubbleWords_orientation (trace : Trace) (k t : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) (i : Fin (2 * t)) :
    (indexedBubbleWords trace k t hx hsep hdel hins i).orientation =
      orientation trace (editEquiv trace t hdel hins i) :=
  bubbleAt_orientation trace k hx hsep (editEquiv trace t hdel hins i)

end DeletionCode.TraceBubbleFamily
