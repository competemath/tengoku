import Tengoku.AlbertFrameTripleInvariants.AlbertLean.JordanLaws
import Tengoku.Seed.LinearAlgebra.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

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

theorem traceN_invariant (g : JordanAut) (x : Coord) :
    traceN (g x) = traceN x := by
  have hc := LinearMap.trace_conj'
    (leftMulLinear productQBilinear x) g.toLinearEquiv
  rw [← leftMul_conj g x] at hc
  rw [traceLeftMulEq, traceLeftMulEq] at hc
  linarith

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

theorem traceCubeDetector_invariant
    (g : JordanAut) (X Y : WitnessTriple) (h : Transports g X Y) :
    traceCubeDetector Y = traceCubeDetector X := by
  rw [traceCubeDetector, traceCubeDetector, W0_natural g X Y h,
    ← g.map_circle, traceForm_invariant]

end AlbertLean
