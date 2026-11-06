/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
module

public import Tengoku.Seed.Algebra.Order.Monoid.WithTop

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict additive monotonicity on `WithBot ℕ`

Mathlib's `WithBot.add_lt_add_of_le_of_lt` / `WithBot.add_lt_add_of_lt_of_le` carry `≠ ⊥`
side conditions; the fully strict version below needs none of them over `ℕ`.
Upstreaming candidate.
-/

@[expose] public section

namespace WithBot

/-- Strict monotonicity of `+` on `WithBot ℕ`: `a < b → c < d → a + c < b + d`.
@isnad1 id=lt.2h4v.s6.b4c89db23b47 from=translated src=- shape=ed79da37 vocab=da92daf6
-/
lemma add_lt_add {a b c d : WithBot ℕ} (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [← WithBot.coe_add]; omega

end WithBot
