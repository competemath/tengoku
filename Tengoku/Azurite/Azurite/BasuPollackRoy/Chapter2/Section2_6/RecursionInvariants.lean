/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RecursionStep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — invariants of the Puiseux root recursion

Towards Puiseux's theorem (Theorem 2.91), the construction iterates `P ↦ P₁ = substPoly P x ξ β`.
For the iteration to keep applying `recursion_step`, the degree must stay odd: `substPoly`
substitutes a degree-`1` polynomial and multiplies by a nonzero constant, so it preserves the
degree (`substPoly_natDegree`). Hence every `Pᵢ` has the same (odd) degree as `P`. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

end Azurite.BPR
