import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.Regressions
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

def w0Theta1Scratch : Coord := fun i =>
  match i.val with
  | 0 => q 3 2 | 1 => q 1 4 | 2 => q (-7) 4 | 3 => q (-1) 3
  | 4 => q (-9) 8 | 5 => q 5857 1944 | 6 => q 1 12 | 7 => q (-48883) 5832
  | 8 => q (-17) 24 | 9 => q (-35) 8 | 10 => q (-1) 36 | 11 => q (-5) 6
  | 12 => 0 | 13 => 0 | 14 => q 1 4 | 15 => q (-5) 4 | 16 => q 13 6
  | 17 => q 2765 648 | 18 => q 3 4 | 19 => q (-1) 2 | 20 => 0
  | 21 => q 1 6 | 22 => 0 | 23 => q 1 2 | 24 => q (-7) 12
  | 25 => q 11 216 | 26 => q 1 12 | _ => 0

theorem W0_theta1_eq_scratch : W0 witnessTheta1 = w0Theta1Scratch := by
  funext k
  fin_cases k <;>
    norm_num [W0, witnessTheta1, structuredProduct_eq_productForm, productForm, theta1E, theta1F, theta1K,
      w0Theta1Scratch, v, q, Fin.ext_iff]

end AlbertLean
