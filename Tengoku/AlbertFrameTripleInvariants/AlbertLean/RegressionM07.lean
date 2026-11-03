import Tengoku.AlbertFrameTripleInvariants.AlbertLean.RegressionM07Data
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.JordanLaws
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

private theorem regression_traceCube_of_trace_zero (x : Coord)
    (hx : traceN x = 0) :
    traceForm x (structuredProduct x x) = 3 * cubicNorm x := by
  have hn := productNorm_eq_cubicNorm x
  simp only [productNorm, productTrace_eq_traceN] at hn
  rw [hx] at hn
  simp only [traceN_structuredProduct_eq_traceForm] at hn
  linear_combination (3 : ℚ) * hn

theorem regressionM07 :
    m07TraceCubeDetector witnessTheta1 = q 656291 62208 ∧
    m07TraceCubeDetector witnessTheta1 ≠ q (-2591357) 62208 := by
  have htrace : traceN m07W0Theta1Scratch = 0 := by
    norm_num [traceN_eq_coords, m07W0Theta1Scratch, q]
  have hval : m07TraceCubeDetector witnessTheta1 = q 656291 62208 := by
    change traceForm (m07W0 witnessTheta1)
      (structuredProduct (m07W0 witnessTheta1) (m07W0 witnessTheta1)) = _
    rw [m07W0_theta1_eq_scratch,
      regression_traceCube_of_trace_zero m07W0Theta1Scratch htrace]
    norm_num [cubicNorm, m07W0Theta1Scratch, v, q]
  refine ⟨hval, ?_⟩
  rw [hval]
  norm_num [q]

end AlbertLean
