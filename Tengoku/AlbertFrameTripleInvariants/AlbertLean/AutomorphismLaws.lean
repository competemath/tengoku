import Tengoku.AlbertFrameTripleInvariants.AlbertLean.JordanLaws
import Tengoku.Seed.LinearAlgebra.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

/--
@isnad1 id=eq.1h1v.s9.b5ec75cb433c from=translated src=- shape=0b725220 vocab=210a8e49
-/
theorem leftMulMatrixTrace_eq_linearMapTrace
    (h : IsQBilinear structuredProduct) (x : Coord) :
    leftMulMatrixTrace x =
      LinearMap.trace ℚ Coord (leftMulLinear h x) := by
  classical
  have hb : ∀ i : Slot, basisVec i = Pi.single i 1 := by
    intro i
    funext j
    simp [basisVec, Pi.single_apply, eq_comm]
  rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ Slot)]
  simp_rw [leftMulMatrixTrace, hb]
  simp [Matrix.trace, leftMulLinear]

/--
@isnad1 id=eq.0h1v.s9.97af9546c605 from=translated src=- shape=202cd466 vocab=e3a2c322
-/
theorem traceLeftMulEq (x : Coord) :
    LinearMap.trace ℚ Coord (leftMulLinear productQBilinear x) =
      9 * traceN x := by
  rw [← leftMulMatrixTrace_eq_linearMapTrace productQBilinear x]
  have hx := printedInvariantsAgree.1 x
  simp only [productTrace] at hx
  linarith

private theorem leftMul_conj (g : JordanAut) (x : Coord) :
    leftMulLinear productQBilinear (g x) =
      g.toLinearEquiv.conj (leftMulLinear productQBilinear x) := by
  apply LinearMap.ext
  intro y
  simp [leftMulLinear, LinearEquiv.conj_apply, g.map_circle]

/--
@isnad1 id=eq.0h2v.s7.7abe08f322a4 from=translated src=- shape=2c1368b9 vocab=093ef66e
-/
theorem traceN_invariant (g : JordanAut) (x : Coord) :
    traceN (g x) = traceN x := by
  have hc := LinearMap.trace_conj'
    (leftMulLinear productQBilinear x) g.toLinearEquiv
  rw [← leftMul_conj g x] at hc
  rw [traceLeftMulEq, traceLeftMulEq] at hc
  linarith

/--
@isnad1 id=eq.0h3v.s8.ca9585cf7dff from=translated src=- shape=e397a319 vocab=80bd9000
-/
theorem traceForm_invariant (g : JordanAut) (x y : Coord) :
    traceForm (g x) (g y) = traceForm x y := by
  rw [← traceN_structuredProduct_eq_traceForm,
    ← traceN_structuredProduct_eq_traceForm, ← g.map_circle,
    traceN_invariant]

private theorem W0_natural
    (g : JordanAut) (X Y : WitnessTriple) (h : Transports g X Y) :
    W0 Y = g (W0 X) := by
  rcases h with ⟨hE, hF, hK⟩
  simp only [W0]
  rw [← hE, ← hF, ← hK]
  simp only [map_sub, g.map_circle]

/--
@isnad1 id=eq.1h3v.s4.505a371d2e12 from=translated src=- shape=7dc06ae2 vocab=836b48f7
-/
theorem traceCubeDetector_invariant
    (g : JordanAut) (X Y : WitnessTriple) (h : Transports g X Y) :
    traceCubeDetector Y = traceCubeDetector X := by
  rw [traceCubeDetector, traceCubeDetector, W0_natural g X Y h,
    ← g.map_circle, traceForm_invariant]

end AlbertLean
