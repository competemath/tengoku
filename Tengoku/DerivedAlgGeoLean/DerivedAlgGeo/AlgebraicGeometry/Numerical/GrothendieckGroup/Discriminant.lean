/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.General
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The numerical discriminant in arbitrary dimension

The Bogomolov discriminant is built from the first two components of the Chern character,
so its definition does not depend on the dimension of the ambient variety. Surface geometry
is where its degree enters the Bogomolov--Gieseker inequality, but the class itself belongs
to the dimension-general numerical API.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace NumericalVarietyData

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData n A N)

/-- The numerical discriminant `Δ(E) = ch₁(E)² - 2 rank(E) ch₂(E)`.

It is defined for a numerical variety of any dimension. When `n < 2`, its membership in the
second graded piece forces it to vanish; when `n = 2`, its degree is the quantity appearing
in the Bogomolov--Gieseker inequality.-/
noncomputable def discriminant (E : N) : A :=
  V.chComp E 1 * V.chComp E 1
    - algebraMap ℚ A (2 * (V.rank E : ℚ)) * V.chComp E 2

/-- **The numerical discriminant is the Mukai self-pairing**, at coefficient
ring `A` with the multiplication of `A` as the bilinear form.

This is one of the three leaves that forced the root to move: it is `A`-valued,
not `ℝ`-valued, and a `ℤ`-only or `ℝ`-only pairing could not parent it. Nothing
else about the root changes — the arity is still three and the triple is
`(rank, ch₁, ch₂)` with the rank pushed into `A` along `ℚ → A`.
@isnad1 id=eq.0h5v.s7.fb5fbddedb66 from=translated src=- shape=6314207a vocab=5e77723b
-/
theorem discriminant_eq_selfPairing (E : N) :
    V.discriminant E
      = Mukai.selfPairing (LinearMap.mul A A)
          (algebraMap ℚ A (V.rank E : ℚ), V.chComp E 1, V.chComp E 2) := by
  rw [Mukai.selfPairing_mk, discriminant]
  show V.chComp E 1 * V.chComp E 1 - algebraMap ℚ A (2 * (V.rank E : ℚ)) * V.chComp E 2
    = V.chComp E 1 * V.chComp E 1
      - 2 * (algebraMap ℚ A (V.rank E : ℚ) * V.chComp E 2)
  rw [map_mul, map_ofNat]
  ring

/-- The discriminant lives in codimension two, independently of the ambient dimension.
@isnad1 id=mem.0h5v.s6.044414a3dd7b from=translated src=- shape=6185469b vocab=958c3cb5
-/
theorem discriminant_mem_piece_two (E : N) :
    V.discriminant E ∈ V.ring.piece 2 := by
  refine Submodule.sub_mem _ ?_ ?_
  · exact V.ring.mul_mem_piece (V.chComp_mem E 1) (V.chComp_mem E 1)
  · exact V.ring.mul_mem_piece (V.ring.algebraMap_mem_piece_zero _) (V.chComp_mem E 2)

/-- Integrating the discriminant pulls its scalar coefficient outside the degree map.
@isnad1 id=eq.0h5v.s8.0b70d1f17bb4 from=translated src=- shape=d25c26e3 vocab=c5a6f3c5
-/
theorem degree_discriminant (E : N) :
    V.ring.degree (V.discriminant E)
      = V.ring.degree (V.chComp E 1 * V.chComp E 1)
        - 2 * (V.rank E : ℚ) * V.ring.degree (V.chComp E 2) := by
  simp only [discriminant, map_sub, V.ring.degree_algebraMap_mul]

end NumericalVarietyData

end AlgebraicGeometry.Numerical
