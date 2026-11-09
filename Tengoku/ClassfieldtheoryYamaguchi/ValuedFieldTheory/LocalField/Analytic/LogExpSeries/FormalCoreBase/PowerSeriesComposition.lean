/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.PowerSeries.Log
import Tengoku.Seed.RingTheory.PowerSeries.WellKnown

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Formal logarithm and exponential composition

This module develops the formal composition identities between Mathlib's
`PowerSeries.log` and `PowerSeries.exp` that are used by the local-field
logarithm and exponential.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PowerSeries

/-- The alternating geometric series is the formal inverse of `1 + X`.-/
theorem alternating_mul_one_add_X
    (A : Type*) [CommRing A] :
    (PowerSeries.mk fun n : ℕ => (-1 : A) ^ n) *
        (1 + PowerSeries.X : PowerSeries A) = 1 := by
  have h :=
    congrArg (PowerSeries.evalNegHom (A := A))
      (PowerSeries.mk_one_mul_one_sub_eq_one A)
  have hmk' :
      PowerSeries.evalNegHom (PowerSeries.mk (1 : ℕ → A)) =
        PowerSeries.mk fun n : ℕ => (-1 : A) ^ n := by
    ext n
    simp [PowerSeries.evalNegHom, PowerSeries.rescale_mk]
  simpa [hmk', sub_eq_add_neg] using h

end PowerSeries

end
