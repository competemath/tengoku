/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_95
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_97
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonStrict
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonOddEdge
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonEdge
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.OddMultiplicityRoot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — one step of the Puiseux root construction

Assembling the pieces (Newton polygon existence + odd-length edge + edge data + odd-multiplicity
root + Lemma 2.95), one step of the construction: from `P` with nonzero constant term and odd
degree (over a real closed coefficient field) we obtain a slope `−ξ`, the constant `β`, a nonzero
root `x ∈ R` of odd multiplicity `r` of the characteristic polynomial, and the recentered
polynomial `P₁ = R(P, E, x, Y)` satisfying the order conclusions of Lemma 2.95 (`recursion_step`).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [IsRealClosed R]

end Azurite.BPR
