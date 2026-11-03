import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

def traceFormGram (x y : Coord) : ℚ :=
  v x 0 * v y 0 + v x 1 * v y 1 + v x 2 * v y 2 +
  v x 3 * v y 4 + v x 4 * v y 3 +
  v x 5 * v y 10 + v x 10 * v y 5 -
  v x 6 * v y 9 - v x 9 * v y 6 +
  v x 7 * v y 8 + v x 8 * v y 7 +
  v x 11 * v y 15 + v x 15 * v y 11 +
  v x 12 * v y 16 + v x 16 * v y 12 +
  v x 13 * v y 17 + v x 17 * v y 13 +
  v x 14 * v y 18 + v x 18 * v y 14 +
  v x 19 * v y 23 + v x 23 * v y 19 +
  v x 20 * v y 24 + v x 24 * v y 20 +
  v x 21 * v y 25 + v x 25 * v y 21 +
  v x 22 * v y 26 + v x 26 * v y 22

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h2v.s3.cc55f9d0a766 from=translated src=- shape=e4af5fdd vocab=6378f7d6
-/
theorem traceForm_eq_gram (x y : Coord) :
    traceForm x y = traceFormGram x y := by
  rw [traceForm_eq_fast]
  simp only [traceLinearForm, spurPairForm, traceFormGram]
  ring

/--
@isnad1 id=eq.0h2v.s3.db83ae98a9a8 from=translated src=- shape=ab795eaa vocab=daa6c08b
-/
theorem traceForm_symmetric (x y : Coord) :
    traceForm x y = traceForm y x := by
  rw [traceForm_eq_gram, traceForm_eq_gram]
  simp only [traceFormGram]
  ring

def traceDualVec (k : Fin 27) : Coord := fun j => traceDualCoeff j k

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h2v.s4.f8dd3362cc99 from=translated src=- shape=a250d8e7 vocab=d90ef801
-/
theorem traceForm_dual_extract (x : Coord) (k : Fin 27) :
    traceForm x (traceDualVec k) = x k := by
  rw [traceForm_eq_gram]
  fin_cases k <;>
    simp [traceFormGram, traceDualVec, traceDualCoeff, traceDualCoeffNat, v, q]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=nondegen.0h0v.s0.07111bb3a179 from=translated src=- shape=45709ebd vocab=07111bb3
-/
theorem traceForm_nondegenerate : NondegenerateTraceForm := by
  intro x hx
  funext k
  have h := hx (traceDualVec k)
  rw [traceForm_dual_extract] at h
  simpa using h

/--
@isnad1 id=tracefor.0h0v.s0.dabd1361bb81 from=translated src=- shape=45709ebd vocab=dabd1361
-/
theorem traceFormSymmetricNondegenerate : TraceFormSymmetricNondegenerate := by
  exact ⟨traceForm_symmetric, traceForm_nondegenerate⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.29ed8baa48e9 from=translated src=- shape=1e70f91f vocab=d2616930
-/
theorem traceN_eq_coords (x : Coord) : traceN x = x 0 + x 1 + x 2 := by
  simpa [traceLinearForm, v] using traceN_eq_traceLinearForm x

/--
@isnad1 id=eq.0h2v.s5.a663f6dac636 from=translated src=- shape=0438c7a3 vocab=57cf969d
-/
theorem traceN_add (x y : Coord) : traceN (x + y) = traceN x + traceN y := by
  simp [traceN_eq_coords]
  ring

/--
@isnad1 id=eq.0h2v.s5.a97404b8d2d3 from=translated src=- shape=0438c7a3 vocab=87a6411f
-/
theorem traceN_sub (x y : Coord) : traceN (x - y) = traceN x - traceN y := by
  simp [traceN_eq_coords]
  ring

/--
@isnad1 id=eq.0h2v.s5.7ead238bd9c6 from=translated src=- shape=803e8aba vocab=163e7cc6
-/
theorem traceN_smul (a : ℚ) (x : Coord) : traceN (a • x) = a * traceN x := by
  simp [traceN_eq_coords]
  ring

/--
@isnad1 id=eq.0h0v.s4.b6198f80037d from=translated src=- shape=1ac31801 vocab=4d1bc073
-/
theorem traceN_zero : traceN (0 : Coord) = 0 := by
  simp [traceN_eq_coords]

/--
@isnad1 id=eq.0h0v.s3.13370a56e394 from=translated src=- shape=b0ae1d2b vocab=f56ffb68
-/
theorem traceN_one : traceN one = 3 := by
  simp [traceN_eq_coords, one, q]
  norm_num

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s3.f1b09ac6f7a3 from=translated src=- shape=0b9453fe vocab=8414684b
-/
theorem traceForm_one_eq_traceN (x : Coord) : traceForm one x = traceN x := by
  rw [traceForm_eq_gram, traceN_eq_coords]
  simp [traceFormGram, one, v, q]

/-- The quadratic coefficient uses the already checked polar pair formula.
@isnad1 id=eq.0h1v.s4.927ef311c4f9 from=translated src=- shape=9c30acf2 vocab=388649be
-/
theorem spurN_eq_spurPairForm (x : Coord) :
    spurN x = spurPairForm x x / 2 := by
  change spurBilinear x x / 2 = spurPairForm x x / 2
  rw [spurBilinear_eq_spurPairForm]

end AlbertLean
