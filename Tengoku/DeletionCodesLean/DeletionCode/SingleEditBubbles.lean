import Tengoku.DeletionCodesLean.DeletionCode.RunBubbleConstruction
import Tengoku.DeletionCodesLean.DeletionCode.BubbleContextGeometry
import Tengoku.DeletionCodesLean.DeletionCode.TraceSeparation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms LocalBubble.geometry` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LocalBubble.spectrum_change` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LocalBubble.source_interval_in_neighborhood` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deletion_bubble` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms insertion_bubble` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms source_intervals_disjoint_of_trace` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Actual interior single edits produce local bubbles, with derived word grammar,
path geometry, spectrum change, and source interval bounds. This combines the
local steps in separated coverage. It does not yet assemble all edits of a
trace into the balanced multi-bubble catalogue presentation.
-/
namespace DeletionCode.SingleEditBubbles

open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation

namespace LocalBubble

variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

/--
@isnad1 id=geometry.2h6v.s5.ddc7e4a0949c from=translated src=- shape=fab9c13e vocab=08dfd43f
-/
theorem geometry (p : LocalBubble k source target pos orientation) (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k) : Geometry p.bubble := by
  have hx' := hx
  rw [p.source_eq] at hx'
  simp only [List.append_assoc] at hx'
  exact context_geometry hk p.bubble p.left_boundary p.right_boundary p.before p.after hx'

/-- The full spectrum change equals the actual positive-minus-negative local
word spectra, not just an abstract signed vector with the right support.
@isnad1 id=eq.0h6v.s7.b7cdd04147fb from=translated src=- shape=e5c7a100 vocab=4ed9deb2
-/
theorem spectrum_change (p : LocalBubble k source target pos orientation) :
    wordSpectrum (listLetters target) target.length (windowLength k) -
      wordSpectrum (listLetters source) source.length (windowLength k) =
      wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length (windowLength k) -
        wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length (windowLength k) := by
  simpa only [p.source_eq, p.target_eq, List.append_assoc] using
    BubbleLocalSpectrum.oriented_context_replacement_vector p.bubble p.before p.after

def sourceInterval (p : LocalBubble k source target pos orientation) : Set ℕ :=
  Set.Ico p.before.length (p.before.length + p.bubble.negativeWord.length)

/--
@isnad1 id=le.0h6v.s5.8dc2263ab42f from=translated src=- shape=0760e5d4 vocab=9f9d0b29
-/
theorem negative_length_le_long (p : LocalBubble k source target pos orientation) :
    p.bubble.negativeWord.length ≤ p.bubble.longWord.length := by
  have hl := lengths p.bubble
  cases ho : p.bubble.orientation <;> simp only [BubbleWord.negativeWord, ho] <;> omega

/--
@isnad1 id=le.0h6v.s5.721e94e696c0 from=translated src=- shape=7b60e1ef vocab=37b70e6f
-/
theorem source_interval_in_bounds (p : LocalBubble k source target pos orientation) :
    sourceInterval p ⊆ Set.Ico 0 source.length := by
  have hlen := congrArg List.length p.source_eq
  simp only [List.length_append] at hlen
  intro r hr
  exact ⟨Nat.zero_le r, by have := hr.2; omega⟩

/-- Every local source letter lies in the paper's prescribed edit neighborhood.
@isnad1 id=le.0h6v.s5.378aed430b44 from=translated src=- shape=e4f790b8 vocab=97bc10a9
-/
theorem source_interval_in_neighborhood (p : LocalBubble k source target pos orientation) :
    sourceInterval p ⊆ neighborhood (windowLength k) pos := by
  have hstart := p.edit_stop
  have hend := p.long_end_le
  have hnegative := negative_length_le_long p
  intro r hr
  have hrlow := hr.1
  have hrhigh := hr.2
  change pos - (windowLength k - 1) ≤ r ∧ r < pos + windowLength k + 1
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  constructor <;> omega

end LocalBubble

/-- A real interior deletion gives a bubble whose geometry and exact spectrum
identity are both derived. No prechosen run, flanks, or paths are inputs.
@isnad1 id=ex.4h3v.s8.0acc061f91d3 from=translated src=- shape=ce36fae9 vocab=c44a2808
-/
theorem deletion_bubble (word : List Bool) (pos k : ℕ) (hk : 1 ≤ k)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    ∃ p : RunBubbleConstruction.LocalBubble k word (word.eraseIdx pos) pos .deletion,
      Geometry p.bubble ∧
      wordSpectrum (listLetters (word.eraseIdx pos)) (word.eraseIdx pos).length (windowLength k) -
        wordSpectrum (listLetters word) word.length (windowLength k) =
        wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length (windowLength k) -
          wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length (windowLength k) := by
  obtain ⟨p⟩ := exists_deletion_bubble word pos k hx hleft hright
  exact ⟨p, LocalBubble.geometry p hk hx, LocalBubble.spectrum_change p⟩

/-- The insertion version keeps the inserted bit and constructs the exact
source and target presentations, including the case of a newly created run.
@isnad1 id=ex.4h4v.s8.d48c75df2891 from=translated src=- shape=9c3ab7d6 vocab=5d23268b
-/
theorem insertion_bubble (word : List Bool) (pos k : ℕ) (bit : Bool) (hk : 1 ≤ k)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    ∃ p : RunBubbleConstruction.LocalBubble k word
        (word.take pos ++ bit :: word.drop pos) pos .insertion,
      p.bubble.bit = bit ∧ Geometry p.bubble ∧
      wordSpectrum (listLetters (word.take pos ++ bit :: word.drop pos))
          (word.take pos ++ bit :: word.drop pos).length (windowLength k) -
        wordSpectrum (listLetters word) word.length (windowLength k) =
        wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length (windowLength k) -
          wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length (windowLength k) := by
  obtain ⟨p, hbit⟩ := exists_insertion_bubble word pos k bit hx hleft hright
  exact ⟨p, hbit, LocalBubble.geometry p hk hx, LocalBubble.spectrum_change p⟩

/-- Two concrete local source intervals inherit disjointness from a 4L gap.
@isnad1 id=disjoint.1h10v.s6.72731d8d2225 from=translated src=- shape=229460fc vocab=cca96c45
-/
theorem source_intervals_disjoint {k a b : ℕ} {source target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation}
    (p : RunBubbleConstruction.LocalBubble k source target₁ a orientation₁)
    (q : RunBubbleConstruction.LocalBubble k source target₂ b orientation₂)
    (hgap : a + 4 * windowLength k ≤ b) :
    Disjoint (LocalBubble.sourceInterval p) (LocalBubble.sourceInterval q) :=
  (neighborhood_disjoint_of_gap (by unfold windowLength; omega) hgap).mono
    (LocalBubble.source_interval_in_neighborhood p) (LocalBubble.source_interval_in_neighborhood q)

/-- The separated alignment supplies the gap for the constructed source intervals.
@isnad1 id=disjoint.4h10v.s7.a1ecf3a0d79d from=translated src=- shape=8c35969e vocab=d79a1cb1
-/
theorem source_intervals_disjoint_of_trace {k : ℕ} {trace : AlignmentTrace.Trace}
    (hsep : FiniteConflictGraph.Separated (4 * windowLength k) trace)
    (i j : Fin trace.length) (hi : FiniteConflictGraph.EditIndex trace i)
    (hj : FiniteConflictGraph.EditIndex trace j) (hne : i ≠ j)
    {target₁ target₂ : List Bool} {orientation₁ orientation₂ : Orientation}
    (p : RunBubbleConstruction.LocalBubble k trace.source target₁ (trace.sourcePosition i.val) orientation₁)
    (q : RunBubbleConstruction.LocalBubble k trace.source target₂ (trace.sourcePosition j.val) orientation₂) :
    Disjoint (LocalBubble.sourceInterval p) (LocalBubble.sourceInterval q) :=
  (source_neighborhood_disjoint (by unfold windowLength; omega) hsep i j hi hj hne).mono
    (LocalBubble.source_interval_in_neighborhood p) (LocalBubble.source_interval_in_neighborhood q)

end DeletionCode.SingleEditBubbles
