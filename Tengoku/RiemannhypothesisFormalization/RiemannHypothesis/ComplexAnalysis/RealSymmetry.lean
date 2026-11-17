/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Data.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real symmetry / conjugation lemmas

Generic lemmas about complex conjugation used by the engine. Isolated here
so `RealZeros.Engine` can import this without pulling in the full
`LogDerivative` or `PoleProbe` files.
-/

namespace OverflowResidueRH

open Complex

/-- `(star z).im = -z.im` — the `Star`-side restatement of `Complex.conj_im`.
@isnad1 id=eq.0h1v.s5.15f0da0e7df9 from=translated src=- shape=5a02da31 vocab=71c00b8c
-/
theorem complex_star_im (ρ : ℂ) : (star ρ).im = -ρ.im := by
  change (starRingEnd ℂ ρ).im = -ρ.im
  exact Complex.conj_im ρ

end OverflowResidueRH
