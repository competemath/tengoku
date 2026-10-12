/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.Module.Primitive
public import Tengoku.Tauceti.TauCeti.Geometry.Toric.Algebraic.Cone
public import Tengoku.Tauceti.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Tengoku.Tauceti.TauCeti.Geometry.Toric.Algebraic.Ray.Basic

/-!
# Primitive generators of toric rays

A rational salient ray in an integral lattice contains a unique primitive lattice vector pointing
along it. This file characterizes that vector as the primitive generator and provides a canonical
choice for each ray of a toric cone.

Primitive generators give canonical integral vectors for the rays of a toric cone. They are the
vectors which enter the definition of a regular cone and, later, its affine monomial coordinates.

## Main declarations

* `TauCeti.Toric.IsPrimitiveGenerator`: a primitive lattice vector on a ray.
* `TauCeti.Toric.IsToricCone.existsUnique_primitiveGenerator`: every ray of a toric cone in an
  integral lattice has a unique primitive generator.
* `TauCeti.Toric.primitiveGenerator`: the resulting canonical lattice vector, with membership,
  nonvanishing, and primitivity lemmas.
* `TauCeti.Toric.IsPrimitiveGenerator.unique`: two primitive generators of the same salient ray in
  an integral lattice are equal.
* `TauCeti.Toric.isPrimitiveGenerator_faceEmbedding`: being a primitive generator of a ray does not
  depend on which cone the ray is viewed as a face of.
* `TauCeti.Toric.IsPrimitiveGenerator.prodInl` and
  `TauCeti.Toric.IsPrimitiveGenerator.prodInr`: primitive generators remain primitive generators
  under the two inclusions into a product cone.

## References

The construction is from §1.2 of W. Fulton, *Introduction to Toric Varieties*, and §1.2 of
D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- A primitive lattice generator of a ray is a primitive lattice vector pointing along the ray. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
def IsPrimitiveGenerator (i : N →+ V) {σ : PointedCone ℝ V}
    (ρ : ToricRay σ) (v : N) : Prop :=
  i v ∈ ρ ∧ IsPrimitive v

/-- The characteristic property of a primitive generator. -/
theorem isPrimitiveGenerator_iff {ρ : ToricRay σ} {v : N} :
    IsPrimitiveGenerator i ρ v ↔ i v ∈ ρ ∧ IsPrimitive v :=
  Iff.rfl

namespace IsPrimitiveGenerator

variable {ρ : ToricRay σ} {v : N}

/-- A primitive generator is primitive. -/
theorem isPrimitive (h : IsPrimitiveGenerator i ρ v) : IsPrimitive v := h.2

end IsPrimitiveGenerator

/-- Being a primitive generator of a ray mentions only the cone underlying the ray, so it is
unaffected by viewing a ray of a face as a ray of the ambient cone. -/
@[simp]
theorem isPrimitiveGenerator_faceEmbedding {τ : PointedCone ℝ V} (hτ : τ.IsFaceOf σ)
    (ρ : ToricRay τ) {v : N} :
    IsPrimitiveGenerator i (ToricRay.faceEmbedding hτ ρ) v ↔ IsPrimitiveGenerator i ρ v := by
  simp [isPrimitiveGenerator_iff]

section Prod

variable {N' V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {τ : PointedCone ℝ V'}

end Prod

namespace IsToricCone

end IsToricCone

end TauCeti.Toric
