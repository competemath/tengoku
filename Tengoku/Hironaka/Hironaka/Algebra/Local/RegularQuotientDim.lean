/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
import Tengoku.Hironaka.Hironaka.Algebra.Local.QuotientParameters
import Tengoku.Hironaka.Hironaka.Algebra.Local.RegularSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular quotients of regular local rings, with the dimension count

If `R` and `R/I` are regular local rings, there is a regular system of parameters `x₁, …, xₙ` of
`R` an initial segment `x₁, …, x_c` of which generates `I`, **and** `dim R/I + c = dim R`
([Sta, Tag 00NR] with [Sta, Tag 00NQ]).  Both halves are proved elsewhere
(`Hironaka/Algebra/Local/QuotientParameters.lean`:
`IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt`;
`Hironaka/Algebra/Local/RegularSystem.lean`:
`isRegularLocalRing_quotient_span_image_lt_and_ringKrullDim`) and are bundled here in the form used
for the Jacobian criterion of analytic spaces (`Hironaka/AnalyticSpace/Jacobian.lean`).
-/

public section

universe u

namespace IsLocalRing

open IsLocalRing _root_.Ideal

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (I : Ideal R)
  [IsRegularLocalRing (R ⧸ I)]

/-- If `R` and `R/I` are regular local rings, there is a regular system of parameters `x` of `R`
an initial segment of length `c` of which generates `I`, and `dim R/I + c = dim R`
([Sta, Tag 00NR] and [Sta, Tag 00NQ]).
@isnad1 id=ex.0h2v.s7.c2e53702a519 from=translated src=- shape=4fe81e25 vocab=b8d7e648
-/
theorem exists_regularSystemOfParameters_of_quotient_and_ringKrullDim :
    ∃ (n c : ℕ) (x : Fin n → R), c ≤ n ∧ (n : WithBot ℕ∞) = ringKrullDim R ∧
      maximalIdeal R = Ideal.span (Set.range x) ∧ I = Ideal.span (x '' {j | j.val < c}) ∧
      ringKrullDim (R ⧸ I) + (c : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨n, c, x, hc, hn, hx, hI⟩ :=
    IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt I
  refine ⟨n, c, x, hc, hn, hx, hI, ?_⟩
  subst hI
  exact (isRegularLocalRing_quotient_span_image_lt_and_ringKrullDim x hx hn hc).2

end IsLocalRing
