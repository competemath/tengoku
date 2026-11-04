/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Tengoku.Seed.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Affine-local relative Proj

This is the affine chart used by the scoped relative-Proj construction.  Over an affine open
`U ⊆ X`, a graded algebra whose degree-zero piece is identified with `Γ(U, ᵊ_U)` gives a
scheme `Proj A` over `U`, hence over `X`.  Finite generation over degree zero makes the local
structure morphism proper by the scheme-level projective-spectrum valuative criterion.

The global relative Proj will glue these charts along localization comparisons.  This file does
not postulate that comparison: it records the actual affine objects and morphisms which the
comparison must identify.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped DirectSum

universe u

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The degree-zero ring homomorphism underlying a graded ring homomorphism.-/
def degreeZeroMap (f : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 where
  toFun x := ⟨f x.1, f.map_mem x.2⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f x.1 y.1)
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.1 y.1)

/--
@isnad1 id=eq.0h8v.s9.ab2da1f1c5e0 from=translated src=- shape=a23fdba7 vocab=319da942
-/
@[simp]
theorem degreeZeroMap_apply (f : 𝒜 →+*ᵍ ℬ) (x : 𝒜 0) :
    degreeZeroMap f x = ⟨f x.1, f.map_mem x.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of `Proj` commutes with its structure map to the degree-zero spectrum.
@isnad1 id=eq.1h7v.s9.49a179cb77f5 from=translated src=- shape=dcd59198 vocab=43d347f8
-/
@[reassoc]
theorem map_toSpecZero (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map f) :
    map f hf ≫ toSpecZero 𝒜 =
      toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (degreeZeroMap f)) := by
  refine (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f,
    awayι_comp_map_assoc f hf s.1.2 (s.2.1 : A) s.2.2]
  rw [awayι_toSpecZero, awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk, degreeZeroMap]

end AlgebraicGeometry.Proj

namespace SchemeRelativeProj

variable (X : Scheme.{u}) (U : X.affineOpens)

/-- A graded algebra over an affine open, with its degree-zero piece identified with the ring of
regular functions on that open.-/
structure AffineData where
  /-- The underlying graded algebra.-/
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra Γ(X, U.1) A]
  /-- The homogeneous pieces.-/
  grading : ℕ → Submodule Γ(X, U.1) A
  [gradedAlgebra : GradedAlgebra grading]
  /-- The standard-grading condition in degree zero.-/
  degreeZeroEquiv : grading 0 ≃ₐ[Γ(X, U.1)] Γ(X, U.1)

namespace AffineData

attribute [instance] commRing algebra gradedAlgebra

variable {X U} (d : AffineData X U)

/-- The affine-local relative projective spectrum.-/
noncomputable abbrev scheme : Scheme.{u} := Proj d.grading

/-- The structure map to the spectrum of the affine base ring.-/
noncomputable def toSpecBase : d.scheme ⟶ Spec (CommRingCat.of Γ(X, U.1)) :=
  Proj.toSpecZero d.grading ≫
    Spec.map d.degreeZeroEquiv.symm.toRingEquiv.toCommRingCatIso.hom

/-- The affine-local relative Proj structure map.-/
noncomputable def toBase : d.scheme ⟶ U.1 :=
  d.toSpecBase ≫ U.2.isoSpec.inv

/-- The same local chart mapped to the ambient base scheme.-/
noncomputable def toAmbient : d.scheme ⟶ X :=
  d.toBase ≫ U.1.ι

/--
@isnad1 id=eq.0h3v.s6.fa6d780b4f6a from=translated src=- shape=2f6a6dab vocab=25174a1e
-/
@[reassoc (attr := simp)]
theorem toBase_comp_openImmersion : d.toBase ≫ U.1.ι = d.toAmbient :=
  rfl

end AffineData

end SchemeRelativeProj
