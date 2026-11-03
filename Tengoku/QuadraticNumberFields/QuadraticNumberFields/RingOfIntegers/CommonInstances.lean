/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Qsqrtd.Basic
import Tengoku.Seed.RingTheory.Int.Basic
import Tengoku.Seed.Tactic.NormNum.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Common Fact Instances for Quadratic Fields

This file provides global `Fact` instances for frequently-used quadratic field parameters
(`d = -1, -3, -5`). These enable cleaner example theorems without verbose inline `letI` blocks.

## Main Instances

- `Fact (Squarefree (-1 : ℤ))` / `Fact ((-1 : ℤ) ≠ 1)` — Gaussian integers
- `Fact (Squarefree (-3 : ℤ))` / `Fact ((-3 : ℤ) ≠ 1)` — Eisenstein integers
- `Fact (Squarefree (-5 : ℤ))` / `Fact ((-5 : ℤ) ≠ 1)` — ℤ[√(-5)]
- `Fact (Squarefree (17 : ℤ))` / `Fact ((17 : ℤ) ≠ 1)` — real field ℚ(√17)
- the remaining Heegner parameters `d = -2, -7, -11, -19, -43, -67, -163`
-/

local notation "ℚ√" d => Qsqrtd d

namespace QuadraticNumberFields

/-! ## Common Fact instances for frequently-used quadratic fields -/

instance : Fact (Squarefree (-5 : ℤ)) := ⟨by
  intro p hp
  exact (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (5 : ℤ)).squarefree p (dvd_neg.mp hp)⟩

instance : Fact ((-5 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (17 : ℤ)) := ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

instance : Fact ((17 : ℤ) ≠ 1) := ⟨by decide⟩

/-! The remaining Heegner parameters; each is the negative of a prime, hence
prime in `ℤ` (via `natAbs`), hence squarefree. -/

end QuadraticNumberFields
