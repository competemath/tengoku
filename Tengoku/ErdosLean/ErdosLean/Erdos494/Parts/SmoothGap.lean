import Tengoku.ErdosLean.ErdosLean.Erdos494.Defs
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.RidoutSmooth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Erdős 494, part D1: gaps between `P`-smooth numbers (non-coprime form).

From `ridout_smooth` (applied with `δ/2`): write `g = gcd(x,y)`, `x = g x'`, `y = g y'`.
If `max(x',y') ≤ B` and `x ≠ y` then `|x - y| ≥ g ≥ max(x,y)/B`, which beats `y^{1-δ}` for
`y` large.  Otherwise `(max/g)^{1-δ/2} ≤ |x'-y'| = |x-y|/g ≤ y^{1-δ}/g`, impossible for `y`
large.  (Note `|x-y| ≤ y^{1-δ}` implies `x ≤ 2y`.) -/

namespace Erdos494

end Erdos494
