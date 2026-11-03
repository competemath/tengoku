import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowProbeTrace
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms eq_of_labelled_probes` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms encoder_square_of_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eq_of_orthogonal_idempotent_labelled_probes` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Labelled ordinary-matrix probes determine a matrix

This specializes the labels to the actual encoder
values `(-1,0,1)` and makes no Albert-algebra assertion.
-/

namespace AlbertLean.Generic.FourRowLabelledProbes

open AlbertLean.Generic.FourRowProbeSeparation
open AlbertLean.Generic.FourRowProbeTrace

variable {K : Type*} [Field K]

/-- The labelled division-free Jordan/trace probe.-/
def labelledProbe (f A : Mat3 K) (i : Fin 3) : K :=
  Matrix.trace ((diagonalUnit i * f + f * diagonalUnit i) * A)

/--
@isnad1 id=eq.0h5v.s6.c0304f51bbc7 from=translated src=- shape=90921965 vocab=8ccbf44d
-/
@[simp] theorem labelledProbe_add (f g A : Mat3 K) (i : Fin 3) :
    labelledProbe (f + g) A i = labelledProbe f A i + labelledProbe g A i := by
  simp [labelledProbe, add_mul, mul_add]
  ring

/--
@isnad1 id=eq.0h5v.s6.a6ff01fbb1ee from=translated src=- shape=90921965 vocab=f7ae93ed
-/
@[simp] theorem labelledProbe_sub (f g A : Mat3 K) (i : Fin 3) :
    labelledProbe (f - g) A i = labelledProbe f A i - labelledProbe g A i := by
  simp [labelledProbe, sub_mul, mul_sub, add_mul]
  ring

/--
@isnad1 id=eq.0h3v.s7.f61dd0254c89 from=translated src=- shape=577c0e4a vocab=cc7bac45
-/
@[simp] theorem labelledProbe_one (A : Mat3 K) (i : Fin 3) :
    labelledProbe 1 A i = 2 * Matrix.trace (diagonalUnit i * A) := by
  simp [labelledProbe, add_mul]
  ring

/-- The literal `(-1,0,1)` encoder attached to the three labels.-/
def encoder (f0 f2 : Mat3 K) : Mat3 K := f2 - f0

/-- Nine labelled probes imply the nine diagonal/first/second-power probes
used by matrix tomography, provided the displayed frame sum and encoder-square
identities hold.-/
theorem eq_of_labelled_probes
    (f0 f1 f2 A B : Mat3 K)
    (hsum : f0 + f1 + f2 = 1)
    (hsquare : encoder f0 f2 * encoder f0 f2 = f0 + f2)
    (hdet : Matrix.det
      (grading * encoder f0 f2 - encoder f0 f2 * grading) ≠ 0)
    (hLabel : ∀ i,
      labelledProbe f0 A i = labelledProbe f0 B i ∧
      labelledProbe f1 A i = labelledProbe f1 B i ∧
      labelledProbe f2 A i = labelledProbe f2 B i) :
    A = B := by
  have hdet' := hdet
  rw [det_grading_commutator] at hdet'
  have hTwo : (2 : K) ≠ 0 := left_ne_zero_of_mul hdet'
  apply eq_of_trace_probes (encoder f0 f2) A B hdet
  · intro i
    apply mul_left_cancel₀ hTwo
    calc
      2 * Matrix.trace (diagonalUnit i * A) =
          labelledProbe (f0 + f1 + f2) A i := by rw [hsum, labelledProbe_one]
      _ = labelledProbe f0 A i + labelledProbe f1 A i + labelledProbe f2 A i := by
        simp only [labelledProbe_add]
      _ = labelledProbe f0 B i + labelledProbe f1 B i + labelledProbe f2 B i := by
        rw [(hLabel i).1, (hLabel i).2.1, (hLabel i).2.2]
      _ = labelledProbe (f0 + f1 + f2) B i := by
        simp only [labelledProbe_add]
      _ = 2 * Matrix.trace (diagonalUnit i * B) := by rw [hsum, labelledProbe_one]
  · intro i
    change labelledProbe (encoder f0 f2) A i = labelledProbe (encoder f0 f2) B i
    simp only [encoder, labelledProbe_sub]
    rw [(hLabel i).1, (hLabel i).2.2]
  · intro i
    change labelledProbe (encoder f0 f2 * encoder f0 f2) A i =
      labelledProbe (encoder f0 f2 * encoder f0 f2) B i
    rw [hsquare]
    simp only [labelledProbe_add]
    rw [(hLabel i).1, (hLabel i).2.2]

/-- For ordinary matrices, idempotence of the two nonzero-labelled pieces and
their two directed orthogonality equations supply the encoder-square premise.
@isnad1 id=eq.4h3v.s9.a2ba6076b93f from=translated src=- shape=04fbd88a vocab=8b7343e0
-/
theorem encoder_square_of_orthogonal
    (f0 f2 : Mat3 K)
    (h0 : f0 * f0 = f0) (h2 : f2 * f2 = f2)
    (h02 : f0 * f2 = 0) (h20 : f2 * f0 = 0) :
    encoder f0 f2 * encoder f0 f2 = f0 + f2 := by
  simp [encoder, sub_mul, mul_sub, h0, h2, h02, h20, add_comm]

/-- Ordinary orthogonal-idempotent wrapper around the minimal transport.-/
theorem eq_of_orthogonal_idempotent_labelled_probes
    (f0 f1 f2 A B : Mat3 K)
    (hsum : f0 + f1 + f2 = 1)
    (h0 : f0 * f0 = f0) (h2 : f2 * f2 = f2)
    (h02 : f0 * f2 = 0) (h20 : f2 * f0 = 0)
    (hdet : Matrix.det
      (grading * encoder f0 f2 - encoder f0 f2 * grading) ≠ 0)
    (hLabel : ∀ i,
      labelledProbe f0 A i = labelledProbe f0 B i ∧
      labelledProbe f1 A i = labelledProbe f1 B i ∧
      labelledProbe f2 A i = labelledProbe f2 B i) :
    A = B := by
  exact eq_of_labelled_probes f0 f1 f2 A B hsum
    (encoder_square_of_orthogonal f0 f2 h0 h2 h02 h20) hdet hLabel

end AlbertLean.Generic.FourRowLabelledProbes
