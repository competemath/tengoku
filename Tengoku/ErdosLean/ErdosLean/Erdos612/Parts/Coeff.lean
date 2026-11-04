import Tengoku.ErdosLean.ErdosLean.Erdos612.Statement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Erdős 612, part: the two coefficients used -/

namespace Erdos612

/--
@isnad1 id=eq.0h0v.s5.1a37b923a46e from=translated src=- shape=4683683d vocab=0c631d79
-/
theorem evenCoeff_two : evenCoeff 2 = 16 / 7 := by
  norm_num [evenCoeff]

/--
@isnad1 id=eq.0h0v.s5.ebe505a4651a from=translated src=- shape=4683683d vocab=dff4c592
-/
theorem oddCoeff_four : oddCoeff 4 = 11 / 4 := by
  norm_num [oddCoeff]

end Erdos612
