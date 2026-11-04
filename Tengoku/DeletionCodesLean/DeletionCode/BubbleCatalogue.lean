import Tengoku.DeletionCodesLean.DeletionCode.BubbleContextGeometry
import Tengoku.DeletionCodesLean.DeletionCode.ConnectedBlocks
import Tengoku.Seed.Algebra.BigOperators.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms wordSpectrum_eq_pathSpectrum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bubble_spectrum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms geometry_unique` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms geometry_endpoints` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms validCatalogue` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rule_spectrum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms catalogueRule` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Concrete local-word geometry and spectra, converted to the catalogue used
by the counting and witness theorems. This module proves the representation
bridge: actual word spectra equal path spectra, and the derived long/short
path geometry supplies the signed catalogue's precise finite index ranges.
-/
namespace DeletionCode.BubbleCatalogue

open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

def pathWord {k : ℕ} (bubble : BubbleWord k) (side : Bool) : List Bool :=
  if side then bubble.positiveWord else bubble.negativeWord

/--
@isnad1 id=eq.0h3v.s4.3430033acc98 from=translated src=- shape=e279251f vocab=b72ab8c9
-/
theorem pathWord_length {k : ℕ} (bubble : BubbleWord k) (side : Bool) :
    (pathWord bubble side).length = PathMemory.pathLength k bubble.header side := by
  cases side <;> simp only [pathWord, PathMemory.pathLength, Bool.false_eq_true,
    ite_false, ite_true]
  · exact bubble.negativeWord_length
  · exact bubble.positiveWord_length

/--
@isnad1 id=le.0h3v.s4.4fdf01cf711e from=translated src=- shape=d90c7f56 vocab=b2753d2f
-/
theorem pathWord_length_ge {k : ℕ} (bubble : BubbleWord k) (side : Bool) :
    windowLength k ≤ (pathWord bubble side).length := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  rw [pathWord_length]
  cases side <;> cases ho : bubble.orientation <;>
    simp only [PathMemory.pathLength, negativeLength, positiveLength, longLength,
      shortLength, BubbleWord.header, ho, Bool.false_eq_true, ite_false, ite_true, windowLength] <;>
    omega

/--
@isnad1 id=eq.0h6v.s5.fe709c92a3c9 from=translated src=- shape=7fdcd8e0 vocab=fe4a2a0d
-/
theorem family_path {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) (side : Bool) :
    (editedFamily words rank).family.path b side = listLetters (pathWord (words b) side) := by
  cases side
  · exact editedFamily_negative words rank b
  · exact editedFamily_positive words rank b

/--
@isnad1 id=eq.0h6v.s5.307c552e4f89 from=translated src=- shape=0be05e48 vocab=71d1e57a
-/
theorem family_extra {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) (side : Bool) :
    (editedFamily words rank).family.extra b side =
      (pathWord (words b) side).length - windowLength k := by
  rw [pathWord_length]
  rfl

/--
@isnad1 id=eq.0h7v.s5.2311901fc7ac from=translated src=- shape=ebf14a37 vocab=a8388463
-/
theorem family_vertex {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) (side : Bool) (i : ℕ) :
    SupportComponents.vertex (editedFamily words rank).family (windowLength k) b side i =
      SpectrumPath.vertexAt (listLetters (pathWord (words b) side)) (windowLength k) i := by
  funext j
  exact congrFun (family_path words rank b side) (i + j.val)

/--
@isnad1 id=eq.1h3v.s5.f3db5d3abc50 from=translated src=- shape=77ca4e45 vocab=f7a46d2a
-/
theorem wordSpectrum_eq_pathSpectrum (x : Letters) (n L : ℕ) (hn : L ≤ n) :
    wordSpectrum x n L = pathSpectrum x L (n - L) := by
  classical
  funext g
  rw [wordSpectrum_eq_windowSum x n L (by omega)]
  unfold windowSum pathSpectrum
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if gram x L i = g then (1 : ℤ) else 0) (n - L + 1)]
  have heq : n + 1 - L = n - L + 1 := by omega
  simp only [heq, Nat.zero_add]

/--
@isnad1 id=eq.0h5v.s6.32c91d69cdf2 from=translated src=- shape=dd902bcd vocab=9669d3ba
-/
theorem bubble_spectrum {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) :
    bubbleSpectrum (editedFamily words rank).family (windowLength k) b =
      wordSpectrum (listLetters (words b).positiveWord) (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord) (words b).negativeWord.length (windowLength k) := by
  have hp : windowLength k ≤ (words b).positiveWord.length := by
    simpa only [pathWord, ite_true] using pathWord_length_ge (words b) true
  have hn : windowLength k ≤ (words b).negativeWord.length := by
    simpa only [pathWord, Bool.false_eq_true, ite_false] using pathWord_length_ge (words b) false
  rw [wordSpectrum_eq_pathSpectrum _ _ _ hp, wordSpectrum_eq_pathSpectrum _ _ _ hn]
  funext g
  simp only [bubbleSpectrum, family_path, family_extra, pathWord, Bool.false_eq_true,
    ite_false, ite_true, Pi.sub_apply]

/--
@isnad1 id=and.0h2v.s6.dd125d52872f from=translated src=- shape=805be5fc vocab=00b9255b
-/
theorem long_short_lengths {k : ℕ} (bubble : BubbleWord k) :
    bubble.longWord.length = windowLength k + (windowLength k - bubble.rho) ∧
      bubble.shortWord.length = windowLength k + (windowLength k - bubble.rho - 1) ∧
      1 ≤ windowLength k - bubble.rho := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, longLength, shortLength,
    BubbleWord.header, windowLength]
  omega

/--
@isnad1 id=eq.4h5v.s6.b58af4b92d0e from=translated src=- shape=19d4c7bf vocab=de1f1d6b
-/
theorem geometry_unique {k : ℕ} (bubble : BubbleWord k) (hg : Geometry bubble)
    (side : Bool) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ (pathWord bubble side).length)
    (hj : j + (windowLength k - 1) ≤ (pathWord bubble side).length)
    (heq : SpectrumPath.vertexAt (listLetters (pathWord bubble side)) (windowLength k) i =
      SpectrumPath.vertexAt (listLetters (pathWord bubble side)) (windowLength k) j) : i = j := by
  have hlens := long_short_lengths bubble
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  have hlong (hi : i ≤ windowLength k - bubble.rho + 1)
      (hj : j ≤ windowLength k - bubble.rho + 1)
      (heq : SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i =
        SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) j) : i = j :=
    congrArg Fin.val (hg.long_simple (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) heq)
  have hshort (hi : i ≤ windowLength k - bubble.rho)
      (hj : j ≤ windowLength k - bubble.rho)
      (heq : SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i =
        SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) j) : i = j :=
    congrArg Fin.val (hg.short_simple (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) heq)
  cases side <;> cases ho : bubble.orientation <;>
    simp only [pathWord, BubbleWord.negativeWord, BubbleWord.positiveWord, ho,
      Bool.false_eq_true, ite_false, ite_true] at hi hj heq
  · exact hlong (by omega) (by omega) heq
  · exact hshort (by omega) (by omega) heq
  · exact hshort (by omega) (by omega) heq
  · exact hlong (by omega) (by omega) heq

/--
@isnad1 id=or.4h4v.s7.d5c2cbb2fc19 from=translated src=- shape=a381418e vocab=c243dfa8
-/
theorem geometry_endpoints {k : ℕ} (bubble : BubbleWord k) (hg : Geometry bubble) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ bubble.negativeWord.length)
    (hj : j + (windowLength k - 1) ≤ bubble.positiveWord.length)
    (heq : SpectrumPath.vertexAt (listLetters bubble.negativeWord) (windowLength k) i =
      SpectrumPath.vertexAt (listLetters bubble.positiveWord) (windowLength k) j) :
    (i = 0 ∧ j = 0) ∨
      (i = bubble.negativeWord.length - windowLength k + 1 ∧
        j = bubble.positiveWord.length - windowLength k + 1) := by
  have hlens := long_short_lengths bubble
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  cases ho : bubble.orientation <;>
    simp only [BubbleWord.negativeWord, BubbleWord.positiveWord, ho] at hi hj heq ⊢
  · have h := hg.endpoints i j (by omega) (by omega) (fun r hr => congrFun heq ⟨r, hr⟩)
    rcases h with h | h
    · exact Or.inl h
    · right; omega
  · have h := hg.endpoints j i (by omega) (by omega) (fun r hr => (congrFun heq ⟨r, hr⟩).symm)
    rcases h with h | h
    · left; exact ⟨h.2, h.1⟩
    · right; omega

/--
@isnad1 id=validcat.3h3v.s7.00f948d370c6 from=translated src=- shape=4cdff4aa vocab=9c68e218
-/
theorem validCatalogue {k ν : ℕ} (words : Fin ν → BubbleWord k)
    (hboundary : ∀ b, (words b).left.getLast? = some (!(words b).bit) ∧
      (words b).right.head? = some (!(words b).bit))
    (hgeometry : ∀ b, Geometry (words b))
    (hdisjoint : ∀ a b : Fin ν, a ≠ b → ∀ sa sb i j,
      i + (windowLength k - 1) ≤ (pathWord (words a) sa).length →
      j + (windowLength k - 1) ≤ (pathWord (words b) sb).length →
      SpectrumPath.vertexAt (listLetters (pathWord (words a) sa)) (windowLength k) i ≠
        SpectrumPath.vertexAt (listLetters (pathWord (words b) sb)) (windowLength k) j) :
    ValidCatalogue words (fun _ => (0 : Fin 1)) := by
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  refine ⟨hboundary, ?_, ?_, ?_⟩
  · intro b side i j heq
    apply Fin.ext
    apply geometry_unique (words b) (hgeometry b) side i.val j.val
    · have hi := i.isLt
      have hlen := pathWord_length_ge (words b) side
      change i.val < (editedFamily words (fun _ => 0)).family.extra b side + 2 at hi
      rw [family_extra] at hi
      omega
    · have hj := j.isLt
      have hlen := pathWord_length_ge (words b) side
      change j.val < (editedFamily words (fun _ => 0)).family.extra b side + 2 at hj
      rw [family_extra] at hj
      omega
    · simpa only [indexedFamily, family_vertex] using heq
  · intro b i j hi hj heq
    change i ≤ (editedFamily words (fun _ => 0)).family.extra b false + 1 at hi
    change j ≤ (editedFamily words (fun _ => 0)).family.extra b true + 1 at hj
    have hn := pathWord_length_ge (words b) false
    have hp := pathWord_length_ge (words b) true
    rw [family_extra] at hi hj
    simp only [pathWord, Bool.false_eq_true, ite_false, ite_true] at hi hj hn hp
    have h := geometry_endpoints (words b) (hgeometry b) i j (by omega)
      (by omega) (by simpa only [indexedFamily, family_vertex, pathWord,
        Bool.false_eq_true, ite_false, ite_true] using heq)
    simpa only [indexedFamily, family_extra, pathWord, Bool.false_eq_true, ite_false, ite_true] using h
  · intro r a _ b _ hab sa sb i j hi hj
    change SupportComponents.vertex (editedFamily words (fun _ => 0)).family _ a sa i ≠
      SupportComponents.vertex (editedFamily words (fun _ => 0)).family _ b sb j
    rw [family_vertex, family_vertex]
    apply hdisjoint a b hab sa sb i j
    · have hn := pathWord_length_ge (words a) sa
      change i ≤ (editedFamily words (fun _ => 0)).family.extra a sa + 1 at hi
      rw [family_extra] at hi
      omega
    · have hn := pathWord_length_ge (words b) sb
      change j ≤ (editedFamily words (fun _ => 0)).family.extra b sb + 1 at hj
      rw [family_extra] at hj
      omega

/--
@isnad1 id=eq.0h4v.s7.0de2114a79b0 from=translated src=- shape=7ed6fb0f vocab=83a932c4
-/
theorem rule_spectrum {k ν : ℕ} (words : Fin ν → BubbleWord k) (rank : Fin ν → ℕ) :
    ruleSpectrum (editedFamily words rank).family (windowLength k) Finset.univ =
      ∑ b, (wordSpectrum (listLetters (words b).positiveWord)
        (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord)
          (words b).negativeWord.length (windowLength k)) := by
  classical
  funext g
  simp only [ruleSpectrum, Finset.sum_apply, Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro b _
  exact congrFun (bubble_spectrum words rank b) g

/-- The signed catalogue constructor with all word-level obligations explicit.
@isnad1 id=catalogu.5h3v.s9.1824b084db33 from=translated src=- shape=e034da41 vocab=a7d19bbd
-/
theorem catalogueRule {t k : ℕ} (words : Fin (2 * t) → BubbleWord k)
    (hboundary : ∀ b, (words b).left.getLast? = some (!(words b).bit) ∧
      (words b).right.head? = some (!(words b).bit))
    (hgeometry : ∀ b, Geometry (words b))
    (hdisjoint : ∀ a b : Fin (2 * t), a ≠ b → ∀ sa sb i j,
      i + (windowLength k - 1) ≤ (pathWord (words a) sa).length →
      j + (windowLength k - 1) ≤ (pathWord (words b) sb).length →
      SpectrumPath.vertexAt (listLetters (pathWord (words a) sa)) (windowLength k) i ≠
        SpectrumPath.vertexAt (listLetters (pathWord (words b) sb)) (windowLength k) j)
    (hdel : (Finset.univ.filter (fun b => (words b).orientation = .deletion)).card = t)
    (hins : (Finset.univ.filter (fun b => (words b).orientation = .insertion)).card = t) :
    ConnectedBlocks.CatalogueRule t k
      (∑ b, (wordSpectrum (listLetters (words b).positiveWord)
        (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord)
          (words b).negativeWord.length (windowLength k))) := by
  classical
  refine ⟨words, validCatalogue words hboundary hgeometry hdisjoint, ?_, ?_⟩
  · intro r
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    simpa only [and_self_left, true_and] using And.intro hdel hins
  · exact rule_spectrum words (fun _ => 0)

end DeletionCode.BubbleCatalogue
