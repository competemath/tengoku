/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Example_2_96
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.CharacteristicPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 Example 2.96, continued — the next Newton-polygon step

The Newton polygon of `P₁` (Example 2.96) has the descending edge `E' = [M₀, M₁] = [(0,4/3),
(1,0)]`. Its slope is `−4/3` (so `ξ = 4/3`), and its characteristic polynomial is
`Q(P₁, E', X) = −3X + 1`. Choosing the root `x' = 1/3` and substituting `X = ε^{4/3}(1/3 + Y)`
yields the first two terms `ε^{1/3} + (1/3)ε^{5/3}` of a Puiseux-series root `x̄` of `P`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [CharZero R]

/-- The slope of the edge `E' = [(0,4/3), (1,0)]` is `−4/3` (so `ξ = 4/3`).
@isnad1 id=eq.0h0v.s5.63f3fb456dfa from=translated src=- shape=fa5d10af vocab=8e45f7f7
-/
theorem slope_E1 : newtonSlope ((0 : ℕ), (4 / 3 : ℚ)) ((1 : ℕ), (0 : ℚ)) = -4 / 3 := by
  rw [newtonSlope]; norm_num

/-- The root of `Q(P₁, E', X) = 1 − 3X` is `x' = 1/3`.
@isnad1 id=isroot.0h1v.s7.b879f86b4b8d from=translated src=- shape=12040e6b vocab=d333c4cd
-/
theorem charPoly_E1_root : (1 - 3 * X : Polynomial R).IsRoot (1 / 3) := by
  simp [Polynomial.IsRoot, Polynomial.eval_sub]

/-- The first two terms `ε^{1/3} + (1/3)ε^{5/3}` of the Puiseux-series root `x̄` of `P`,
obtained from `x̄ = ε^{1/3}(1 + ε^{4/3}(1/3 + Y))` by dropping the `Y`-term.-/
noncomputable def rootApprox : PuiseuxSeries R :=
  puiseuxMonomial (1 / 3) + (1 / 3) * puiseuxMonomial (5 / 3)

end Azurite.BPR
