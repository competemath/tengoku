/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Families.RichaudDegert
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Units.Pell

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Units in Explicit Families

Explicit Pell-type unit candidates for the classical Richaud-Degert shapes
`d = n² ± 1` and `d = n² ± 2` (the `a = 1` Richaud-Degert families).

## Main definitions

* `HasExplicitUnitCandidate d`: `d` admits an explicit nontrivial solution of
  `x² - d·y² = ±1`.

## Main results

* `isPellUnitSolution_sq_sub_one` and friends: explicit solutions for the
  four families `d = n² ± 1`, `d = n² ± 2`.
* `hasExplicitUnitCandidate_richaudDegert_one`: every `a = 1` Richaud-Degert
  parameter with shift `k ∈ {-2, -1, 1, 2}` has an explicit unit candidate.
* `HasExplicitUnitCandidate.exists_unit_ne_one`: an explicit candidate yields
  a unit of `ℤ[√d]` different from `±1`.
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
local notation "ℚ√" d => Qsqrtd d

namespace QuadraticNumberFields
namespace Units

open QuadraticAlgebra

/-- `d` admits an explicit nontrivial solution of `x² - d·y² = ±1`, hence an
explicit unit of `ℤ[√d]` other than `±1`.-/
def HasExplicitUnitCandidate (d : ℤ) : Prop :=
  ∃ x y : ℤ, y ≠ 0 ∧ (IsPellSolution d 1 x y ∨ IsPellSolution d (-1) x y)

/-- `(n, 1)` solves the norm-one Pell equation for `d = n² - 1`.
@isnad1 id=ispellun.0h1v.s5.9bf232ea9480 from=translated src=- shape=ec1a4110 vocab=02ccc4ca
-/
theorem isPellUnitSolution_sq_sub_one (n : ℤ) : IsPellUnitSolution (n ^ 2 - 1) n 1 := by
  unfold IsPellUnitSolution IsPellSolution
  ring

/-- `(n, 1)` solves the norm-`-1` Pell equation for `d = n² + 1`.
@isnad1 id=ispellso.0h1v.s5.1ebd5ecf1fad from=translated src=- shape=fd7134d4 vocab=897602ff
-/
theorem isPellSolution_neg_one_sq_add_one (n : ℤ) : IsPellSolution (n ^ 2 + 1) (-1) n 1 := by
  unfold IsPellSolution
  ring

/-- `(n² + 1, n)` solves the norm-one Pell equation for `d = n² + 2`.
@isnad1 id=ispellun.0h1v.s6.0a973671f3cb from=translated src=- shape=ebe5be7f vocab=104cc2f5
-/
theorem isPellUnitSolution_sq_add_two (n : ℤ) :
    IsPellUnitSolution (n ^ 2 + 2) (n ^ 2 + 1) n := by
  unfold IsPellUnitSolution IsPellSolution
  ring

/-- `(n² - 1, n)` solves the norm-one Pell equation for `d = n² - 2`.
@isnad1 id=ispellun.0h1v.s6.218492212b9e from=translated src=- shape=ebe5be7f vocab=02ccc4ca
-/
theorem isPellUnitSolution_sq_sub_two (n : ℤ) :
    IsPellUnitSolution (n ^ 2 - 2) (n ^ 2 - 1) n := by
  unfold IsPellUnitSolution IsPellSolution
  ring

/-- The family `d = n² - 1` has an explicit unit candidate.
@isnad1 id=hasexpli.0h1v.s5.54acae9981ef from=translated src=- shape=81b9bbc4 vocab=c9e8aa58
-/
theorem hasExplicitUnitCandidate_sq_sub_one (n : ℤ) :
    HasExplicitUnitCandidate (n ^ 2 - 1) :=
  ⟨n, 1, one_ne_zero, Or.inl (isPellUnitSolution_sq_sub_one n)⟩

/-- The family `d = n² + 1` has an explicit unit candidate.
@isnad1 id=hasexpli.0h1v.s5.3e4171d8d772 from=translated src=- shape=81b9bbc4 vocab=c88a5ccf
-/
theorem hasExplicitUnitCandidate_sq_add_one (n : ℤ) :
    HasExplicitUnitCandidate (n ^ 2 + 1) :=
  ⟨n, 1, one_ne_zero, Or.inr (isPellSolution_neg_one_sq_add_one n)⟩

/-- The family `d = n² + 2` has an explicit unit candidate for `n ≠ 0`.
@isnad1 id=hasexpli.1h1v.s5.19dd55612580 from=translated src=- shape=cf54dd47 vocab=c88a5ccf
-/
theorem hasExplicitUnitCandidate_sq_add_two {n : ℤ} (hn : n ≠ 0) :
    HasExplicitUnitCandidate (n ^ 2 + 2) :=
  ⟨n ^ 2 + 1, n, hn, Or.inl (isPellUnitSolution_sq_add_two n)⟩

/-- The family `d = n² - 2` has an explicit unit candidate for `n ≠ 0`.
@isnad1 id=hasexpli.1h1v.s5.8b56dfce52a7 from=translated src=- shape=cf54dd47 vocab=c9e8aa58
-/
theorem hasExplicitUnitCandidate_sq_sub_two {n : ℤ} (hn : n ≠ 0) :
    HasExplicitUnitCandidate (n ^ 2 - 2) :=
  ⟨n ^ 2 - 1, n, hn, Or.inl (isPellUnitSolution_sq_sub_two n)⟩

/-- The `a = 1` Richaud-Degert parameter is `n² + k`.
@isnad1 id=eq.0h2v.s5.3ac83af8851a from=translated src=- shape=95a0573e vocab=e9d2dfae
-/
theorem richaudDegertD_one (n k : ℤ) : Families.richaudDegertD 1 n k = n ^ 2 + k := by
  unfold Families.richaudDegertD
  ring

/-- Every `a = 1` Richaud-Degert parameter `n² + k` with shift
`k ∈ {-2, -1, 1, 2}` and `n ≠ 0` has an explicit unit candidate.
@isnad1 id=hasexpli.2h2v.s6.8dbf8ac0879b from=translated src=- shape=945ef726 vocab=0c249d04
-/
theorem hasExplicitUnitCandidate_richaudDegert_one {k : ℤ} (n : ℤ) (hn : n ≠ 0)
    (hk : k = -2 ∨ k = -1 ∨ k = 1 ∨ k = 2) :
    HasExplicitUnitCandidate (Families.richaudDegertD 1 n k) := by
  rw [richaudDegertD_one]
  rcases hk with rfl | rfl | rfl | rfl
  · exact (by ring_nf : n ^ 2 + -2 = n ^ 2 - 2) ▸ hasExplicitUnitCandidate_sq_sub_two hn
  · exact (by ring_nf : n ^ 2 + -1 = n ^ 2 - 1) ▸ hasExplicitUnitCandidate_sq_sub_one n
  · exact hasExplicitUnitCandidate_sq_add_one n
  · exact hasExplicitUnitCandidate_sq_add_two hn

/-- An explicit unit candidate yields a unit of `ℤ[√d]` different from `±1`.
@isnad1 id=ex.1h1v.s8.1bdf99d71c67 from=translated src=- shape=82401937 vocab=51e3d210
-/
theorem HasExplicitUnitCandidate.exists_unit_ne_one {d : ℤ}
    (h : HasExplicitUnitCandidate d) :
    ∃ u : (Zsqrtd d)ˣ, u ≠ 1 ∧ u ≠ -1 := by
  obtain ⟨x, y, hy, hsol⟩ := h
  rcases hsol with hpos | hneg
  · exact ⟨IsPellUnitSolution.unit hpos, IsPellUnitSolution.unit_ne_one hpos hy,
      IsPellUnitSolution.unit_ne_neg_one hpos hy⟩
  · exact ⟨IsPellSolution.negOneUnit hneg, IsPellSolution.negOneUnit_ne_one hneg hy,
      IsPellSolution.negOneUnit_ne_neg_one hneg hy⟩

end Units
end QuadraticNumberFields
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
