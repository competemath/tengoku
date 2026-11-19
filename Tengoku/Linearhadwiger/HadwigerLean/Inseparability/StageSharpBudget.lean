import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.ScaleCeilEstimates
import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.SharpWovenBudget

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The paper's logarithmic stage parameters fit the sharp woven budget. -/

namespace HadwigerLean.Inseparability

/--
@isnad1 id=le.3h3v.s6.fc9b19e044d4 from=translated src=- shape=cae1457d vocab=553d59aa
-/
theorem stage_sharp_woven_budget
    (t p C : ℕ) (ht : 3 ≤ t)
    (hp : p < stageCount t) (hC : 9000000 ≤ C) :
    1000000 *
      HadwigerLean.RootedDensity.cliqueMatchingScale
        (2 * stageBlockSize t) ((4 * p + 1) * stageBlockSize t) ≤
      ((C * t : ℕ) : ℝ) := by
  exact sharp_woven_stage_budget t p (stageBlockSize t) C
    (stageBlockSize_root_log_bound t ht)
    (stageIndex_mul_block_le t p ht hp)
    (stageBlockSize_le t ht) hC

end HadwigerLean.Inseparability
