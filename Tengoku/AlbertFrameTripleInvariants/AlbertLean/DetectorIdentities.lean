import Tengoku.AlbertFrameTripleInvariants.AlbertLean.JordanLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

private theorem traceForm_square_formula (x : Coord) :
    traceForm x (structuredProduct x x) =
      traceN x ^ 3 - 3 * traceN x * spurN x + 3 * cubicNorm x := by
  have hs := productSpur_eq_spurN x
  have hn := productNorm_eq_cubicNorm x
  simp only [productSpur, productNorm, productTrace_eq_traceN] at hs hn
  rw [traceN_structuredProduct_eq_traceForm] at hs
  rw [traceN_structuredProduct_eq_traceForm] at hn
  rw [traceN_structuredProduct_eq_traceForm] at hn
  linear_combination (3 : ℚ) * hn - (3 * traceN x) * hs

/-- The commutator word `W0 X` has trace zero. The detector is the trace of
its Jordan cube, which need not vanish.
@isnad1 id=eq.0h1v.s3.4482b71df3a6 from=translated src=- shape=f6b6ad72 vocab=807b29e7
-/
theorem traceN_W0 (X : WitnessTriple) : traceN (W0 X) = 0 := by
  rw [W0, traceN_sub, traceN_structuredProduct_eq_traceForm,
    traceN_structuredProduct_eq_traceForm,
    ← traceFormAssociative, ← traceFormAssociative,
    productCommutative X.cE X.cF, sub_self]

/--
@isnad1 id=eq.1h1v.s4.3c71cb2f0cd3 from=translated src=- shape=01b1bf08 vocab=37fdf9c0
-/
theorem detectorFactorThree :
    ∀ X : WitnessTriple, traceN (W0 X) = 0 →
      traceCubeDetector X = 3 * cubicNormDetector X := by
  intro X h
  rw [traceCubeDetector, cubicNormDetector, traceForm_square_formula]
  rw [h]
  ring

end AlbertLean
