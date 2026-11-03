import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.Regressions
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessDetector
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

private theorem regression_product_neg_neg (x : Coord) :
    structuredProduct (-x) (-x) = structuredProduct x x := by
  simp only [show -x = (-1 : ℚ) • x by simp,
    productQBilinear.2.1, productQBilinear.2.2.2, smul_smul]
  norm_num

private theorem regression_traceForm_neg_left (x y : Coord) :
    traceForm (-x) y = -traceForm x y := by
  rw [← traceN_structuredProduct_eq_traceForm,
    ← traceN_structuredProduct_eq_traceForm,
    show -x = (-1 : ℚ) • x by simp, productQBilinear.2.1, traceN_smul]
  ring

/--
@isnad1 id=and.0h0v.s5.2553d0ef0f81 from=translated src=- shape=aeba8697 vocab=4dc42e1a
-/
theorem regressionM06 :
    m06TraceCubeDetector witnessTheta1 = q 2591357 62208 ∧
    m06TraceCubeDetector witnessTheta1 ≠ q (-2591357) 62208 := by
  have hm06 : m06W0 witnessTheta1 = -W0 witnessTheta1 := by
    simp [m06W0, W0]
  have hval : m06TraceCubeDetector witnessTheta1 = q 2591357 62208 := by
    change traceForm (m06W0 witnessTheta1)
      (structuredProduct (m06W0 witnessTheta1) (m06W0 witnessTheta1)) = _
    rw [hm06, regression_product_neg_neg, regression_traceForm_neg_left]
    change -traceCubeDetector witnessTheta1 = q 2591357 62208
    rw [witnessDetectorValues.1]
    norm_num [q]
  refine ⟨hval, ?_⟩
  rw [hval]
  norm_num [q]

end AlbertLean
