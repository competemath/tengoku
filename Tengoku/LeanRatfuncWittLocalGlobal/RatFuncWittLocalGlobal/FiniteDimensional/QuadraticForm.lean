/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.FiniteDimensional.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quadratic-map bridge for finite diagonal forms

This file exposes the finite diagonal expression as Mathlib's quadratic-map
API.  The bridge is intentionally unconditional and keeps the existing
`Diagonal.Isotropic` predicate as the public diagonal interface.
-/

open scoped BigOperators

namespace RatFuncWittLocalGlobal

namespace Diagonal

variable {F ι : Type*}

/-- The quadratic map represented by the finite diagonal coefficient vector `a`.-/
def diagonalQuadraticForm [Field F] [Fintype ι] (a : ι → F) :
    QuadraticMap F (ι → F) F :=
  QuadraticMap.weightedSumSquares F a

/--
@isnad1 id=eq.0h4v.s7.fb47d0bcdade from=translated src=- shape=8530c7d2 vocab=0dbba9cf
-/
@[simp]
theorem diagonalQuadraticForm_apply [Field F] [Fintype ι]
    (a x : ι → F) :
    diagonalQuadraticForm a x = diagonalValue a x := by
  simp [diagonalQuadraticForm, diagonalValue, smul_eq_mul, pow_two]

/-- Diagonal isotropy is non-anisotropy of its associated quadratic map.
@isnad1 id=iff.0h3v.s6.ff128214e463 from=translated src=- shape=c8316ef7 vocab=20965818
-/
theorem isotropic_iff_not_diagonalQuadraticForm_anisotropic
    [Field F] [Fintype ι] (a : ι → F) :
    Isotropic a ↔ ¬(diagonalQuadraticForm a).Anisotropic := by
  simpa [Isotropic, diagonalValue] using
    (QuadraticMap.not_anisotropic_iff_exists (diagonalQuadraticForm a)).symm

end Diagonal
end RatFuncWittLocalGlobal
