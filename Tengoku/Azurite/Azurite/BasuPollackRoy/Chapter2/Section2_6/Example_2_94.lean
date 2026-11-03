/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.CharacteristicPolynomial
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Infinitesimal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 Example 2.94 — a Newton diagram

For `P(X) = ε − 2ε²X² − X³ + εX⁴ + εX⁵ ∈ R⟨⟨ε⟩⟩[X]` we compute the Newton diagram. Each `Xⁱ`
coefficient is a single ε-monomial, so each nonzero column contributes one point, and the Newton
diagram is `{(0,1), (2,2), (3,0), (4,1), (5,1)}`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- The polynomial `P(X) = ε − 2ε²X² − X³ + εX⁴ + εX⁵` of Example 2.94.-/
noncomputable def exP : Polynomial (PuiseuxSeries R) :=
  monomial 0 puiseuxEps + monomial 2 (-(2 * puiseuxEps ^ 2))
    + monomial 3 (-1) + monomial 4 puiseuxEps + monomial 5 puiseuxEps

/-- A single term `single e c` (with `c ≠ 0`) is nonzero at `ε^r` exactly when `r = e`.
@isnad1 id=iff.1h4v.s7.e4917ae529c1 from=translated src=- shape=29230232 vocab=f8d0de09
-/
theorem single_coeff_ne_zero_iff {e r : ℚ} {c : R} (hc : c ≠ 0) :
    (HahnSeries.single e c).coeff r ≠ 0 ↔ r = e := by
  rw [HahnSeries.coeff_single]; split <;> simp_all

/-! ## Orders, initial coefficients, and slopes -/

/-- The slope of the edge `E = [M₀, M₃] = [(0,1), (3,0)]` is `−1/3` (so `ξ_E = 1/3`).
@isnad1 id=eq.0h0v.s5.4bea4181cf05 from=translated src=- shape=ed6324d8 vocab=8e45f7f7
-/
theorem slope_E : newtonSlope ((0 : ℕ), (1 : ℚ)) ((3 : ℕ), (0 : ℚ)) = -1 / 3 := by
  rw [newtonSlope]; norm_num

/-- The slope of the edge `F = [M₃, M₅] = [(3,0), (5,1)]` is `1/2` (so `ξ_F = −1/2`).
@isnad1 id=eq.0h0v.s5.4e32967745a2 from=translated src=- shape=bb77f1c4 vocab=edbff43b
-/
theorem slope_F : newtonSlope ((3 : ℕ), (0 : ℚ)) ((5 : ℕ), (1 : ℚ)) = 1 / 2 := by
  rw [newtonSlope]; norm_num

/-! ## The two edges and their characteristic polynomials -/

/-! ## The full Newton-polygon certificate -/

end Azurite.BPR
