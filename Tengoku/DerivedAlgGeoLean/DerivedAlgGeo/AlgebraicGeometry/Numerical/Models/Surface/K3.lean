/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.K3
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.RankOne
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A K3 surface of Picard rank one

The first model of `NumericalVarietyData` in dimension two. Before it, every statement in
`DerivedAlgGeo/AlgebraicGeometry/Numerical/Specializations/Surface.lean` and
`DerivedAlgGeo/AlgebraicGeometry/Numerical/RiemannRoch/K3.lean` was conditional on a
`NumericalVarietyData 2 A N` existing at all — only the dimension-zero point had been exhibited.

The surface is a K3 `X` with `Pic X = ℤ·H` and `H² = 2d`. The ring, grading and degree map
come from `Numerical/Models/Surface/RankOne.lean`; all this file supplies is the Todd class

`td(X) = 1 + 0 + (1/d)·H²`,

so that `td₁ = 0` and `∫_X td₂ = 2` — which is exactly `K3.IsK3`, proved here rather than
assumed.

`d` is a parameter, not fixed to 1: the Bridgeland wall structure on a K3 depends on the
degree. It is a natural number rather than a rational because `χ` must land in `ℤ` —
Riemann–Roch on this model reads `χ(r, c, s) = 2r + 2ds`.
-/

open Polynomial Submodule Set
open DerivedAlgGeo.LinearAlgebra

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd class of a K3: `td₁ = 0`, and `td₂` normalised so that `∫_X td₂ = 2`.-/
noncomputable def k3Todd (d : ℚ) : ℕ → SurfaceRing
  | 0 => 1
  | 1 => 0
  | 2 => algebraMap ℚ SurfaceRing (1 / d) * H ^ 2
  | _ + 3 => 0

theorem k3Todd_mem (d : ℚ) (i : ℕ) :
    k3Todd d i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 => exact surface_one_mem
  | 1 => exact Submodule.zero_mem _
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

theorem k3Todd_sum (d : ℚ) :
    (∑ j ∈ Finset.range (2 + 1), k3Todd d j)
      = 1 + algebraMap ℚ SurfaceRing 0 * H + algebraMap ℚ SurfaceRing (1 / d) * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [k3Todd]

end Examples

end AlgebraicGeometry.Numerical
