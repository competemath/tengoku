import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace PDT

noncomputable section

/-- The quartic `x^4 - x - 1`, whose real root is `Q`.-/
def fQ : ℚ[X] := X ^ 4 - X - 1

/-- The cubic `x^3 - x - 1`, whose real root is `ρ`.-/
def fρ : ℚ[X] := X ^ 3 - X - 1

end

end PDT
