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
theorem traceForm_eq_gram (x y : Coord) :
    traceForm x y = traceFormGram x y := by
  rw [traceForm_eq_fast]
  simp only [traceLinearForm, spurPairForm, traceFormGram]
  ring

theorem traceForm_symmetric (x y : Coord) :
    traceForm x y = traceForm y x := by
  rw [traceForm_eq_gram, traceForm_eq_gram]
  simp only [traceFormGram]
  ring

def traceDualVec (k : Fin 27) : Coord := fun j => traceDualCoeff j k

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem traceForm_dual_extract (x : Coord) (k : Fin 27) :
    traceForm x (traceDualVec k) = x k := by
  rw [traceForm_eq_gram]
  fin_cases k <;>
    simp [traceFormGram, traceDualVec, traceDualCoeff, traceDualCoeffNat, v, q]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem traceForm_nondegenerate : NondegenerateTraceForm := by
  intro x hx
  funext k
  have h := hx (traceDualVec k)
  rw [traceForm_dual_extract] at h
  simpa using h

theorem traceFormSymmetricNondegenerate : TraceFormSymmetricNondegenerate := by
  exact ⟨traceForm_symmetric, traceForm_nondegenerate⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem traceN_eq_coords (x : Coord) : traceN x = x 0 + x 1 + x 2 := by
  simpa [traceLinearForm, v] using traceN_eq_traceLinearForm x

theorem traceN_add (x y : Coord) : traceN (x + y) = traceN x + traceN y := by
  simp [traceN_eq_coords]
  ring

theorem traceN_sub (x y : Coord) : traceN (x - y) = traceN x - traceN y := by
  simp [traceN_eq_coords]
  ring

theorem traceN_smul (a : ℚ) (x : Coord) : traceN (a • x) = a * traceN x := by
  simp [traceN_eq_coords]
  ring

theorem traceN_zero : traceN (0 : Coord) = 0 := by
  simp [traceN_eq_coords]

theorem traceN_one : traceN one = 3 := by
  simp [traceN_eq_coords, one, q]
  norm_num

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem traceForm_one_eq_traceN (x : Coord) : traceForm one x = traceN x := by
  rw [traceForm_eq_gram, traceN_eq_coords]
  simp [traceFormGram, one, v, q]

/-- The quadratic coefficient uses the already checked polar pair formula.-/
theorem spurN_eq_spurPairForm (x : Coord) :
    spurN x = spurPairForm x x / 2 := by
  change spurBilinear x x / 2 = spurPairForm x x / 2
  rw [spurBilinear_eq_spurPairForm]

end AlbertLean
