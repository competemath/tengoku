import Tengoku.AlbertFrameTripleInvariants.AlbertLean.DetectorIdentities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem theta1_detector :
    traceCubeDetector witnessTheta1 = q (-2591357) 62208 := by
  rw [detectorFactorThree witnessTheta1 (traceN_W0 witnessTheta1)]
  simp only [cubicNormDetector, W0, witnessTheta1,
    structuredProduct_eq_productForm]
  norm_num [cubicNorm, productForm, theta1E, theta1F, theta1K, v, q]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem thetaM_detector :
    traceCubeDetector witnessThetaM = q (-1782559) 62208 := by
  rw [detectorFactorThree witnessThetaM (traceN_W0 witnessThetaM)]
  simp only [cubicNormDetector, W0, witnessThetaM,
    structuredProduct_eq_productForm]
  norm_num [cubicNorm, productForm, thetaME, thetaMF, thetaMK, v, q]

theorem witnessDetectorValues :
    traceCubeDetector witnessTheta1 = q (-2591357) 62208 ∧
    traceCubeDetector witnessThetaM = q (-1782559) 62208 ∧
    traceCubeDetector witnessTheta1 ≠ traceCubeDetector witnessThetaM := by
  refine ⟨theta1_detector, thetaM_detector, ?_⟩
  rw [theta1_detector, thetaM_detector]
  norm_num [q]

end AlbertLean
