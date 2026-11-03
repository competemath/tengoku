import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.Regressions
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

def m07W0Theta1Scratch : Coord := fun i =>
  match i.val with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => q 7 24 | 4 => q 7 12
  | 5 => q 1849 972 | 6 => q 37 24 | 7 => q (-3407) 1458
  | 8 => q 37 48 | 9 => q (-35) 48 | 10 => q (-109) 72
  | 11 => q (-5) 6 | 12 => q 5 6 | 13 => 0 | 14 => q 1 2
  | 15 => q (-35) 12 | 16 => q 7 2 | 17 => q 1135 324
  | 18 => q 13 12 | 19 => q (-1) 4 | 20 => 0 | 21 => q 1 6
  | 22 => q (-1) 6 | 23 => q (-3) 4 | 24 => q 155 324
  | 25 => q (-151) 216 | 26 => q 89 108 | _ => 0

/--
@isnad1 id=eq.0h0v.s2.fc0a9d71f09d from=translated src=- shape=4b736592 vocab=a79ae093
-/
theorem m07W0_theta1_eq_scratch :
    m07W0 witnessTheta1 = m07W0Theta1Scratch := by
  funext k
  fin_cases k <;>
    norm_num [m07W0, witnessTheta1, structuredProduct_eq_productForm, productForm, theta1E, theta1F, theta1K,
      m07W0Theta1Scratch, v, q, Fin.ext_iff]

end AlbertLean
