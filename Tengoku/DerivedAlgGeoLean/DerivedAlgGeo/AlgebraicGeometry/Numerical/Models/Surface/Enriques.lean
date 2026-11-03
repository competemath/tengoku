/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.RankOne
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.Enriques
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A polarisation slice of the Enriques numerical lattice

**This model is a slice, not the Enriques numerical lattice.** `Num(Y)` of a
genuine Enriques surface is `U ⊕ E₈(−1)`, of rank ten; what is built here is the
rank-one sublattice `ℤ·H` spanned by one polarisation class with `H² = 2d`, which
is a legitimate slice because the Enriques lattice is even. Nothing below has
Picard rank one as a hypothesis or as a conclusion, and no isotropic sequence,
no rank-ten form and no lattice-theoretic Enriques invariant is visible from
here. The rank-ten lattice is a separate lane.

What the slice carries is the Todd class

`td(Y) = 1 + 0 + (1/(2d))·H²`,

so that `td₁ = 0` and `∫_Y td₂ = χ(O_Y) = 1` — strictly between the K3's `2`
and the abelian surface's `0`. Riemann–Roch on this model reads
`χ(r, c, s) = r + 2ds`.

## What the numerical shadow cannot see

On an Enriques surface `2K_Y = 0` with `K_Y ≠ 0` in `Pic` — the geometric
formulation is the business of the geometric surface lane, and no bridge from
this numerical model is claimed in either direction. Torsion dies in the
numerical quotient, so here `td₁ = -K/2` is *zero*, exactly as it is for the
abelian surface: `td₁` cannot detect the torsion —
`enriquesToddComp_one` and `abelianToddComp_one` are the same equation. What
separates the two models is `∫td₂ = 1` versus `0`, not anything `ω_Y`-shaped.

The carrier is the shared rank-one surface ring of
`Models/Surface/RankOne.lean` — "a new model costs a Todd class and nothing
else" — which the K3, abelian and projective-plane models use as siblings of
this one. As `AlgebraicGeometry/Surface/K3.lean` records for its own model in
"What this file does not do", the numerical-to-geometric bridge is
Hirzebruch–Riemann–Roch and does not exist at the pin.

The rank coefficient is `∫td₂ = 1` rather than the K3's `2` or the abelian
surface's `0`, so `χ` increases by exactly one when the rank does: `χ` is onto
`ℤ` here, lands in `2ℤ` on the K3 model, and cannot see the rank at all on
the abelian one.

## Main definitions

* `enriquesNumericalVariety` — the model.
* `standardEnriquesNumericalVariety` — a named degree-one witness.

## Main results

* `enriquesNumericalVariety_satisfiesHRR` — the presentation satisfies HRR.
* `enriques_isEnriques` — the model satisfies the numerical Enriques
  signature.
* `enriquesChiStructureSheaf` — `∫_Y td₂ = χ(O_Y) = 1`.
* `enriquesToddComp_one` — `td₁ = 0`: the canonical class is numerically
  trivial, though not trivial in `Pic`.

## References

* Li, Nuer, Stellari, Zhao, *A refined Derived Torelli Theorem for Enriques
  surfaces*, arXiv:1912.04332.
-/

open Polynomial Submodule Set
open DerivedAlgGeo.LinearAlgebra

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd class of an Enriques surface: `td₁ = 0` because the 2-torsion
canonical class is numerically trivial, and `td₂` normalised so that
`∫_Y td₂ = 1`.-/
noncomputable def enriquesTodd (d : ℚ) : ℕ → SurfaceRing
  | 0 => 1
  | 1 => 0
  | 2 => algebraMap ℚ SurfaceRing (1 / (2 * d)) * H ^ 2
  | _ + 3 => 0

theorem enriquesTodd_mem (d : ℚ) (i : ℕ) :
    enriquesTodd d i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 => exact surface_one_mem
  | 1 => exact Submodule.zero_mem _
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

theorem enriquesTodd_sum (d : ℚ) :
    (∑ j ∈ Finset.range (2 + 1), enriquesTodd d j)
      = 1 + algebraMap ℚ SurfaceRing 0 * H
        + algebraMap ℚ SurfaceRing (1 / (2 * d)) * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [enriquesTodd]

end Examples

end AlgebraicGeometry.Numerical
