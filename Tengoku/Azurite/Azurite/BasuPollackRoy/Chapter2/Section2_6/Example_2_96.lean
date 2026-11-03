/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Example_2_94
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxMonomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 Example 2.96 — the substitution `P₁ = ε^{−1}P(ε^{1/3}(1+X))`

Continuing Example 2.94, we choose the edge `E` (with `ξ = 1/3`, `β = 1`) and the root `x = 1`
of the characteristic polynomial `Q(P,E,X) = 1 − X³` (multiplicity `1`), and substitute
`X = ε^{1/3}(1 + X)`, dividing by `ε^β = ε`:

`P₁(X) = ε^{−1} P(ε^{1/3}(1 + X))`.

We verify the explicit expansion of `P₁` from BPR, and that it exhibits Lemma 2.95(a): every
coefficient `bᵢ` has `o(bᵢ) ≥ 0`, with `o(b₀) > 0` and `o(b₁) = 0` (since `x = 1` has
multiplicity `r = 1`).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- **`P₁(X) = ε^{−1} P(ε^{1/3}(1 + X))`** (Example 2.96).-/
noncomputable def exP1 : Polynomial (PuiseuxSeries R) :=
  C (puiseuxMonomial (-1)) * (exP.comp (C (puiseuxMonomial (1 / 3)) * (1 + X)))

/-! ### The monomial-coefficient reductions -/

/-! ### The coefficients `bᵢ` and Lemma 2.95(a) -/

/-- The order of a Puiseux series is unchanged by negation.-/
theorem puiseuxOrder_neg (a : PuiseuxSeries R) : puiseuxOrder R (-a) = puiseuxOrder R a := by
  rw [puiseuxOrder, puiseuxOrder, Subfield.coe_neg, HahnSeries.orderTop_neg]

/-! ### The Newton diagram of `P₁` -/

theorem coe_neg_one : ((-1 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 (-1) := by
  rw [show ((-1 : PuiseuxSeries R) : HahnSeries ℚ R) = (-1 : HahnSeries ℚ R) from by norm_cast,
    ← HahnSeries.C_apply]; norm_num

end Azurite.BPR
