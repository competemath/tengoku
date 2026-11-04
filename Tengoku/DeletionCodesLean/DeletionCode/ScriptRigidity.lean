import Tengoku.DeletionCodesLean.DeletionCode.EditRigidity
import Tengoku.DeletionCodesLean.DeletionCode.SingleEditScripts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms shared_source_letters` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms within_one_unique` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms within_one_spectrum_boolean` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms within_one_vertex_path_injective` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The shared-source and uniqueness lemma for genuine list edit scripts. Concrete
edits, output lengths, and their letter functions are derived from scripts of
cost at most one, so no origin labelling or unedited-block premise is supplied
by the caller. The explicit-edit theorem covers every fixed edit realization.
-/
namespace DeletionCode.ScriptRigidity

open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins

/-- Equal long windows after genuine single edits have a common source block
at a common window offset. The edits and their source labellings are realized
from the original scripts.
@isnad1 id=ex.7h6v.s8.06a59b9e3276 from=translated src=- shape=df1e78d0 vocab=70832a31
-/
theorem shared_source_letters {k : ℕ} (hk : 1 ≤ k) (x y z : List Bool)
    (hx : KUnique (listLetters x) x.length k)
    (hy : WithinEdits 1 x y) (hz : WithinEdits 1 x z) (a b : ℕ)
    (ha : a + (windowLength k - 1) ≤ y.length)
    (hb : b + (windowLength k - 1) ≤ z.length)
    (hag : Agree (listLetters y) a (listLetters z) b (windowLength k - 1)) :
    ∃ e f : Edit, e.Valid x.length ∧ f.Valid x.length ∧
      e.outputLength x.length = y.length ∧ f.outputLength x.length = z.length ∧
      e.word (listLetters x) = listLetters y ∧ f.word (listLetters x) = listLetters z ∧
      ∃ s r : ℕ, s + k ≤ windowLength k - 1 ∧ r + k ≤ x.length ∧
        ∀ i, i < k →
          e.origin (a + s + i) = some (r + i) ∧
          f.origin (b + s + i) = some (r + i) := by
  obtain ⟨e, he, hlen, hword⟩ := SingleEditScripts.within_one_realized hy
  obtain ⟨f, hf, hlen', hword'⟩ := SingleEditScripts.within_one_realized hz
  refine ⟨e, f, he, hf, hlen, hlen', hword, hword', ?_⟩
  apply EditRigidity.shared_source_letters hk (listLetters x) hx e f he hf a b
  · simpa only [hlen] using ha
  · simpa only [hlen'] using hb
  · simpa only [hword, hword'] using hag

/-- Every actual word within one edit of a k-unique word is (L-1)-unique.
@isnad1 id=kunique.3h3v.s5.ce099728205b from=translated src=- shape=ba5449e2 vocab=1769186d
-/
theorem within_one_unique {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y) :
    KUnique (listLetters y) y.length (windowLength k - 1) := by
  obtain ⟨e, he, hlen, hword⟩ := SingleEditScripts.within_one_realized hy
  simpa only [hlen, hword] using EditRigidity.one_edit_unique hk (listLetters x) hx e he

/--
@isnad1 id=or.3h4v.s6.db7cbe84246e from=translated src=- shape=3566a94c vocab=5b5e61ed
-/
theorem within_one_spectrum_boolean {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y) :
    ∀ g, SignedSupport.wordSpectrum (listLetters y) y.length (windowLength k) g = 0 ∨
      SignedSupport.wordSpectrum (listLetters y) y.length (windowLength k) g = 1 :=
  SpectrumPath.spectrum_boolean (listLetters y) y.length (windowLength k)
    (within_one_unique hk x y hx hy)

/-- The de Bruijn walk after one edit is simple, including its endpoint vertices.
@isnad1 id=injectiv.4h3v.s7.122479180f28 from=translated src=- shape=b98aeb72 vocab=ae06ab53
-/
theorem within_one_vertex_path_injective {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y)
    (hlen : windowLength k ≤ y.length) :
    Function.Injective (fun i : Fin (y.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters y) (windowLength k) i.val) :=
  SpectrumPath.vertex_path_injective (listLetters y) y.length (windowLength k)
    (by unfold windowLength; omega) hlen (within_one_unique hk x y hx hy)

end DeletionCode.ScriptRigidity
