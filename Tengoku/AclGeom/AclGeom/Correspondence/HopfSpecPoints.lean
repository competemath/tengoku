/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.AlgebraicGeometry.Group.Affine
import Tengoku.Seed.RingTheory.HopfAlgebra.Convolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Points of affine group schemes

For a Hopf algebra `S` over a commutative ring `R`, Mathlib makes `Spec S` a group object over
`Spec R` and identifies morphisms out of `Spec R` with `R`-algebra maps `S → R`, the group law
becoming convolution (`Spec.mapMulEquiv`). This module transports that identification to sections
of the monoidal unit `𝟙_` of schemes over `Spec R`, the form used for points of algebraic groups
(`hopfPointsMulEquiv`).

The named consumers are the concrete multiplicative and additive group schemes realizing the
coordinates of blueprint Lemma `affine-action` (8.4a), and the curve-coset invocations in the proofs
of Theorems `addcorr` and `mulcorr`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the point group of an affine group scheme is identified with the convolution group.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u

/-- Precomposition with an isomorphism is an isomorphism of the monoids of morphisms into a
monoid object.-/
def precompMulEquiv {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y M : C}
    [MonObj M] (e : X ≅ Y) : (Y ⟶ M) ≃* (X ⟶ M) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := Iso.inv_hom_id_assoc e f
  right_inv f := Iso.hom_inv_id_assoc e f
  map_mul' f g := MonObj.comp_mul e.hom f g

variable (R : Type u) [CommRing R]

/-- The monoidal unit of schemes over `Spec R` is `Spec R` over itself.-/
def unitIsoSpecAsOver : 𝟙_ (Over (Spec (.of R))) ≅ (Spec (.of R)).asOver (Spec (.of R)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _
    rw [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])

/-- The `R`-points of the affine group scheme of a Hopf algebra `S` form the convolution group of
`R`-algebra maps `S → R`.-/
def hopfPointsMulEquiv (S : Type u) [CommRing S] [HopfAlgebra R S] :
    (𝟙_ (Over (Spec (.of R))) ⟶ (Spec (.of S)).asOver (Spec (.of R))) ≃*
      WithConv (S →ₐ[R] R) :=
  (precompMulEquiv (unitIsoSpecAsOver R).symm).trans Spec.mapMulEquiv.symm

/-- The point corresponding to an `R`-algebra map is its `Spec`.-/
theorem hopfPointsMulEquiv_symm_apply_left (S : Type u) [CommRing S] [HopfAlgebra R S]
    (f : S →ₐ[R] R) :
    ((hopfPointsMulEquiv R S).symm (WithConv.toConv f)).left =
      Spec.map (CommRingCat.ofHom f.toRingHom) := by
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [Category.id_comp]

end

end AclGeom
