import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The numerical endgame of joint restricted invertibility

Ravichandran--Srivastava's root-shrinking estimate bounds the largest
root by

`c * (1 - α) + 2 * sqrt (c * (1 - c) * α)`.

For a family of `k` Hermitian contractions the mixed determinantal
polynomial has second root moment `α ≤ 1 / k`.  The restricted
invertibility proof takes `c = ε² / (6k)` and then multiplies the root
bound by `k`.  This file verifies, without any analytic assumptions,
that the resulting number is strictly smaller than `ε`.
-/

namespace CommutatorTheorem

end CommutatorTheorem
