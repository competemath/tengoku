import Tengoku.DeletionCodesLean.DeletionCode.SpectrumLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms shared_prefix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shared_suffix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms context_replacement` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms oriented_context_replacement` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms oriented_context_replacement_vector` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The local replacement identity for the actual bubble grammar. The repeated
run gives equal first and last L-1 letters without any flank-bit or path
assumption. Consequently arbitrary unchanged exterior words cancel from the
integer spectrum difference, in either edit orientation.
-/

namespace DeletionCode.BubbleLocalSpectrum

open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization

/-- Removing the last run bit leaves the first L-1 letters unchanged.
@isnad1 id=agree.0h2v.s5.b62de7112463 from=translated src=- shape=70dc0003 vocab=76801d78
-/
theorem shared_prefix {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) 0 (listLetters bubble.shortWord) 0
      (windowLength k - 1) := by
  rw [← bubble.delete_longWord]
  intro i hi
  simp only [Nat.zero_add, deleteAt, editOffset, ite_eq_left hi]

/-- The two local words end in the same actual word d^(rho-1) B.
@isnad1 id=agree.0h2v.s6.8b3e0977e435 from=translated src=- shape=2a7bc324 vocab=36a844f6
-/
theorem shared_suffix {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) (bubble.longWord.length + 1 - windowLength k)
      (listLetters bubble.shortWord) (bubble.shortWord.length + 1 - windowLength k)
      (windowLength k - 1) := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hleft := bubble.left_length
  have hlstart : bubble.longWord.length + 1 - windowLength k = bubble.left.length + 1 := by
    rw [bubble.longWord_length]
    simp only [longLength, BubbleWord.header]
    unfold windowLength at *
    omega
  have hsstart : bubble.shortWord.length + 1 - windowLength k = bubble.left.length := by
    rw [bubble.shortWord_length]
    simp only [shortLength, longLength, BubbleWord.header]
    unfold windowLength at *
    omega
  have hrep : List.replicate bubble.rho bubble.bit =
      bubble.bit :: List.replicate (bubble.rho - 1) bubble.bit := by
    conv_lhs => rw [show bubble.rho = (bubble.rho - 1) + 1 by omega, List.replicate_succ]
  rw [hlstart, hsstart]
  intro i _hi
  change listLetters (bubble.left ++ (List.replicate bubble.rho bubble.bit ++ bubble.right))
      (bubble.left.length + 1 + i) =
    listLetters (bubble.left ++ (List.replicate (bubble.rho - 1) bubble.bit ++ bubble.right))
      (bubble.left.length + i)
  have hindex : bubble.left.length + 1 + i = bubble.left.length + (i + 1) := by omega
  rw [hindex, listLetters_append_right, listLetters_append_right, hrep]
  simp only [List.cons_append, listLetters, List.getD_cons_succ]

/--
@isnad1 id=and.0h2v.s5.113e60c1a027 from=translated src=- shape=cf03d0a9 vocab=fe420f94
-/
theorem length_bounds {k : ℕ} (bubble : BubbleWord k) :
    windowLength k ≤ bubble.longWord.length + 1 ∧
      windowLength k ≤ bubble.shortWord.length + 1 := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, shortLength, longLength,
    BubbleWord.header, windowLength]
  omega

/-- Replacing the longer local word by the shorter changes the full spectrum
by precisely the local spectrum difference, with arbitrary unchanged context.
@isnad1 id=eq.0h5v.s7.0b160f6cd271 from=translated src=- shape=db24e845 vocab=fc71943e
-/
theorem context_replacement {k : ℕ} (bubble : BubbleWord k) (x y : List Bool)
    (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.shortWord ++ y)))
        (x ++ (bubble.shortWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.longWord ++ y)))
        (x ++ (bubble.longWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.shortWord) bubble.shortWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.longWord) bubble.longWord.length (windowLength k) g := by
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  simpa only [List.length_append, Nat.add_assoc] using
    SpectrumLocalization.context_replacement x bubble.longWord bubble.shortWord y
      (windowLength k) hL (length_bounds bubble).1 (length_bounds bubble).2
      (shared_prefix bubble) (shared_suffix bubble) g

/-- The local replacement formula uses the actual negative and positive
grammar words in both deletion and insertion orientations.
@isnad1 id=eq.0h5v.s7.b17b0b909ea5 from=translated src=- shape=db24e845 vocab=3599767f
-/
theorem oriented_context_replacement {k : ℕ} (bubble : BubbleWord k) (x y : List Bool)
    (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.positiveWord ++ y)))
        (x ++ (bubble.positiveWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.negativeWord ++ y)))
        (x ++ (bubble.negativeWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.positiveWord) bubble.positiveWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.negativeWord) bubble.negativeWord.length (windowLength k) g := by
  have h := context_replacement bubble x y g
  cases ho : bubble.orientation with
  | deletion =>
    simpa only [BubbleWord.positiveWord, BubbleWord.negativeWord, ho] using h
  | insertion =>
    simp only [BubbleWord.positiveWord, BubbleWord.negativeWord, ho]
    omega

/-- Function equality of the actual signed integer spectrum vectors.
@isnad1 id=eq.0h4v.s7.43141226e99c from=translated src=- shape=6b0f18f3 vocab=3599767f
-/
theorem oriented_context_replacement_vector {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    wordSpectrum (listLetters (x ++ (bubble.positiveWord ++ y)))
        (x ++ (bubble.positiveWord ++ y)).length (windowLength k) -
      wordSpectrum (listLetters (x ++ (bubble.negativeWord ++ y)))
        (x ++ (bubble.negativeWord ++ y)).length (windowLength k) =
      wordSpectrum (listLetters bubble.positiveWord) bubble.positiveWord.length (windowLength k) -
        wordSpectrum (listLetters bubble.negativeWord) bubble.negativeWord.length (windowLength k) := by
  funext g
  exact oriented_context_replacement bubble x y g

end DeletionCode.BubbleLocalSpectrum
