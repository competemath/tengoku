/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Tengoku.Tauceti.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
import Tengoku.Tauceti.TauCeti.Data.Fin.Sum

/-!
# Regular toric cones and regular fans

A toric cone is *regular*, or smooth, when its primitive ray generators can be completed to a
single integral basis of the lattice. This is the combinatorial condition under which the affine
chart of the cone is a mixed chart `ℂ ^ k × (ℂ ^ *) ^ (n - k)` rather than a singular affine toric
variety, so it is the hypothesis carried by the downstream mixed-chart and complex-manifold
constructions.

Regularity is defined here as the conjunction of `TauCeti.Toric.IsToricCone` with the existence of
an *extending basis*: an integral basis `b` of the lattice together with an injection `r` of the
rays of the cone into the basis indices such that `b (r ρ)` is the primitive generator of the ray
`ρ`. The toric-cone hypothesis separately enforces lattice rationality, salience, and finite
generation; the basis condition alone would be vacuous whenever the cone's `ToricRay` type is
empty.

Two extending bases of the same cone cannot differ at the ray indices, because a ray of a toric
cone in an integral lattice has only one primitive generator. This pins the block form of the
transition matrix between two extending bases: every ray column is a standard column supported at
the matching ray row, so splitting the index set of each basis into its rays and a common
complement, compatibly with the two ray indexings, the matrix is `[[1, B], [0, D]]` with `D`
unimodular. The analytic layer consumes exactly this shape: changing the extending basis keeps the
boundary coordinates, twists them by `B`, and acts on the torus coordinates by `D`.

## Main declarations

* `TauCeti.Toric.IsExtendingBasis`: an integral basis whose vectors at the ray indices are the
  primitive ray generators.
* `TauCeti.Toric.IsRegularCone`: a toric cone admitting an extending basis.
* `TauCeti.Toric.isRegularCone_bot`: the zero cone, whose affine chart is the dense torus, is
  regular.
* `TauCeti.Toric.isRegularCone_hull_singleton`: the cone spanned by a primitive lattice vector,
  whose affine chart is the mixed chart `ℂ × (ℂ ^ *) ^ (n - 1)` with a single boundary coordinate,
  is regular.
* `TauCeti.Toric.IsRegularCone.of_isFaceOf` and `TauCeti.Toric.IsRegularCone.face`: a face of a
  regular cone is regular. Since the pairwise intersections of the cones of a fan are faces, this
  also makes the overlaps of the affine charts of a regular fan regular.
* `TauCeti.Toric.IsRegularCone.prod`: a product of regular cones is regular for the product lattice
  map.
* `TauCeti.Toric.IsRegularCone.card_toricRay_le_finrank`: a regular cone has at most as many rays
  as the rank of the lattice, which is the count that gives the dimensions of its mixed chart.
* `TauCeti.Toric.IsRegularCone.exists_basis_sum`: an extending basis indexed by the rays followed
  by a finite complementary type, as required by regular affine coordinates.
* `TauCeti.Toric.IsExtendingBasis.basis_apply_eq`,
  `TauCeti.Toric.IsExtendingBasis.repr_basis_apply` and
  `TauCeti.Toric.IsExtendingBasis.toMatrix_apply`: the salient ray columns of the transition matrix
  relating two extending bases.
* `TauCeti.Toric.isUnit_det_toMatrix_submatrix_inr`: for two bases indexed by a splitting of the
  index set into the rays of the cone and a common complement, both extending the primitive ray
  generators, the complementary block of the transition matrix is unimodular.
* `TauCeti.Toric.IsExtendingBasis.isUnit_det_toMatrix_compl` and
  `TauCeti.Toric.IsExtendingBasis.exists_isUnit_det_toMatrix_compl`: the complementary block of
  that transition matrix is unimodular, for compatible splittings of the two index sets into the
  rays and a common complement, and such a splitting exists.
* `TauCeti.Toric.Fan.IsRegular`: a fan all of whose cones are regular, together with the
  regularity of the fan of a regular cone and of subfans.

## Implementation notes

`TauCeti.Toric.IsRegularCone` extends `TauCeti.Toric.IsToricCone`, so lattice rationality,
salience and finite generation of a regular cone are reached by dot notation through the parent
structure rather than by forwarding lemmas.

The index type of an extending basis is `Fin n` for an unconstrained `n` rather than
`Fin (Module.finrank ℤ N)`. The two are interchangeable, since `Module.finrank_eq_card_basis`
identifies `n` with the rank and `TauCeti.Toric.IsRegularCone.exists_basis_finrank` produces the
second form on demand, but the unconstrained index avoids transporting a basis along an equality
of natural numbers every time one is built.

## References

The mathematics is §1.2 and Proposition 1.2.16 of W. Fulton, *Introduction to Toric Varieties*,
and §§1.2 and 1.3 of D. Cox, J. Little and H. Schenck, *Toric Varieties*, where a regular cone is
called smooth.
-/

public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {σ τ : PointedCone ℝ V}

/-! ### Extending bases -/

/-- An integral basis `b` of `N` *extends the primitive ray generators* of a cone `σ` along an
injection `r` of the rays of `σ` into the basis indices when the basis vector `b (r ρ)` is the
primitive generator of the ray `ρ`. -/
structure IsExtendingBasis (i : N →+ V) {σ : PointedCone ℝ V} {n : ℕ}
    (b : Module.Basis (Fin n) ℤ N) (r : ToricRay σ ↪ Fin n) : Prop where
  /-- The basis vector indexed by a ray is the primitive generator of that ray. -/
  isPrimitiveGenerator_apply : ∀ ρ : ToricRay σ, IsPrimitiveGenerator i ρ (b (r ρ))

/-! ### Regular cones -/

/-- A toric cone is *regular*, or smooth, when some integral basis of the lattice extends its
primitive ray generators. The toric-cone hypothesis is part of the definition: it enforces
lattice rationality, salience, and finite generation, while the basis condition alone would be
vacuous for any cone whose `ToricRay` type is empty. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
structure IsRegularCone (i : N →+ V) (σ : PointedCone ℝ V) : Prop extends IsToricCone i σ where
  /-- Some integral basis extends the primitive ray generators of the cone. -/
  exists_basis : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (r : ToricRay σ ↪ Fin n),
    IsExtendingBasis i b r

namespace IsRegularCone

end IsRegularCone

/-! ### The zero cone and the cone of a ray -/

/-- The zero cone is regular. Its affine chart is the dense torus of the lattice, which is
therefore a smooth chart of every toric variety built from a nonempty fan. -/
@[simp]
theorem isRegularCone_bot (hi : IsIntegralLattice i) :
    IsRegularCone i (⊥ : PointedCone ℝ V) := by
  have _ := hi.free
  have _ := hi.finite
  exact ⟨isToricCone_bot i, Module.finrank ℤ N, Module.finBasis ℤ N,
    Function.Embedding.ofIsEmpty, ⟨fun ρ ↦ isEmptyElim ρ⟩⟩

/-! ### Faces -/

namespace IsRegularCone

/-- A face of a regular cone is regular: its rays are rays of the ambient cone, with the same
primitive generators, so an extending basis of the ambient cone restricts to one of the face. -/
theorem of_isFaceOf (hσ : IsRegularCone i σ) (hτ : τ.IsFaceOf σ) : IsRegularCone i τ := by
  obtain ⟨n, b, r, hb⟩ := hσ.exists_basis
  refine ⟨hσ.toIsToricCone.of_isFaceOf hτ, n, b, (ToricRay.faceEmbedding hτ).trans r,
    ⟨fun ρ ↦ ?_⟩⟩
  exact (isPrimitiveGenerator_faceEmbedding hτ ρ).1 (hb.isPrimitiveGenerator_apply _)

/-- Every element of Mathlib's face lattice of a regular cone is a regular cone. Since the
pairwise intersection of two cones of a fan is a face of each of them, the overlaps of the affine
charts of a regular fan are again charts of regular cones. -/
theorem face (hσ : IsRegularCone i σ) (F : σ.Face) : IsRegularCone i F.toPointedCone :=
  hσ.of_isFaceOf F.isFaceOf

end IsRegularCone

/-! ### Products -/

/-! ### Two extending bases -/

namespace IsExtendingBasis

variable {n n' : ℕ} {b : Module.Basis (Fin n) ℤ N} {b' : Module.Basis (Fin n') ℤ N}
  {r : ToricRay σ ↪ Fin n} {r' : ToricRay σ ↪ Fin n'}

end IsExtendingBasis

namespace IsRegularCone

end IsRegularCone

/-! ### Regular fans -/

namespace Fan

/-- A fan is *regular*, or smooth, when every one of its cones is regular. This is the hypothesis
under which the analytic realization of the fan is a complex manifold. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
def IsRegular (Φ : Fan i) : Prop := ∀ ⦃σ⦄, σ ∈ Φ.cones → IsRegularCone i σ

/-- The characteristic property of a regular fan. -/
@[simp]
theorem isRegular_iff {Φ : Fan i} :
    Φ.IsRegular ↔ ∀ σ ∈ Φ.cones, IsRegularCone i σ := Iff.rfl

/-- The fan of a regular cone is regular: its cones are the faces of that cone. -/
theorem isRegular_ofCone (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) :
    (ofCone hi hσ.toIsToricCone).IsRegular :=
  fun _ hτ ↦ hσ.of_isFaceOf ((mem_ofCone_cones hi hσ.toIsToricCone).1 hτ)

/-- A subfan of a regular fan is regular. -/
theorem IsRegular.subfan {Φ : Fan i} (hΦ : Φ.IsRegular) (S : Set (PointedCone ℝ V))
    (hS : S ⊆ Φ.cones) (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S) :
    (Φ.subfan S hS hface).IsRegular := fun _ hσ ↦ hΦ (hS (by rwa [Φ.subfan_cones] at hσ))

end Fan

end TauCeti.Toric
