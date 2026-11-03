/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.RankOne
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A polarised abelian surface

The third surface model, and the degenerate one: on an abelian surface `c₁ = c₂ = 0`, so

`td(A) = 1 + 0 + 0`

and Riemann–Roch collapses to `χ(E) = ∫_A ch₂(E)`. Both other terms of `Surface.chi_eq`
vanish, and they vanish for different reasons than on a K3 — there `∫td₂ = 2` keeps the rank
term alive, here it is `0`.

That makes this the surface model where `χ` sees neither the rank nor `c₁`, which is the
two-dimensional shadow of `CalabiYauThreefold.chi_eq_of_chComp_eq`. It is worth having for
exactly that reason: a Bridgeland central charge normalised against `χ` degenerates here in
a way it does not on a K3, and a statement that silently assumed `∫td₂ ≠ 0` would pass on
both other surface models.

`A` carries a polarisation `H` of type `(1, d)`, so `∫_A H² = 2d`. The evenness is an input,
not something this model checks: it is Riemann–Roch on `A` itself — `χ(O_A(H)) = H²/2` must
be an integer — and `[O_A(H)]` is one of the classes the integral lattice `SurfaceNum` below
does *not* contain, so the model cannot evaluate it.

## Chern-character coordinates

These are the same as the K3's — a class `(r, c, s)` has `ch = r + c·H + s·H²` in the basis
`1, H, H²` — so `k3ChCoeff` is reused rather than copied. That is the design
`Models/Surface/RankOne.lean` states outright: within Picard rank one, a new model costs a
Todd class and nothing else.

`s` ranging over `ℤ` makes `N` the sublattice of classes whose `ch₂` is an integer multiple
of `H²`, which is a genuine restriction — `O(mH)` has `ch₂ = (m²/2)H²` and so lies in it
only for even `m`. The K3 model carries the same restriction and for the same reason; where
a model needs the full lattice it must reparametrise, as `Models/Surface/ProjectivePlane.lean`
does.

## Main definitions

* `abelianNumericalVariety` — the model.

## Main results

* `abelianChiStructureSheaf` — `∫_A td₂ = χ(O_A) = 0`.
* `abelianToddComp_one` — `td₁ = 0`, i.e. the canonical class is trivial.
* `abelianChi_eq_of_chComp_two_eq` — `χ` is blind to the rank and to `c₁`.
-/

open Polynomial Submodule Set
open DerivedAlgGeo.LinearAlgebra

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd class of an abelian surface: `c₁ = c₂ = 0`, so every component above `td₀`
vanishes.-/
noncomputable def abelianTodd : ℕ → SurfaceRing
  | 0 => 1
  | _ + 1 => 0

/--
@isnad1 id=mem.0h1v.s8.80c732951c47 from=translated src=- shape=47eb5a58 vocab=9533a54e
-/
theorem abelianTodd_mem (i : ℕ) :
    abelianTodd i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 => exact surface_one_mem
  | _ + 1 => exact Submodule.zero_mem _

/--
@isnad1 id=eq.0h0v.s8.2a66974cb394 from=translated src=- shape=24ddbddc vocab=da386e7d
-/
theorem abelianTodd_sum :
    (∑ j ∈ Finset.range (2 + 1), abelianTodd j)
      = 1 + algebraMap ℚ SurfaceRing 0 * H + algebraMap ℚ SurfaceRing 0 * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [abelianTodd]

end Examples

end AlgebraicGeometry.Numerical
