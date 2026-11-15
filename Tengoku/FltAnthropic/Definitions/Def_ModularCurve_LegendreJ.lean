import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ModularCurve

def legendreJ {K : Type*} [Field K] (t : K) : K :=
  2 ^ 8 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2)

end ModularCurve
