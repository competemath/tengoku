/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.RingTheory.AlgebraicIndependent.Basic
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An algebraically closed extension with four fresh elements

The correspondence theorems of the hard kernel (`addcorr`, `mulcorr`) are stated, as in the
blueprint, for an arbitrary pair `k ⊆ Ω` of algebraically closed fields.  Their two-pair cores
relocate generic points along elements fresh over the data, which need not exist in `Ω`.
`FreshAmbient Ω`, the algebraic closure of the rational function field in four variables over
`Ω`, is an algebraically closed extension of `Ω` of transcendence degree at least four over any
subfield (`four_le_trdeg_freshAmbient`).  Both theorems pass to it and pull their polynomial
conclusions back along the injective embedding.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5).
-/

namespace AclGeom

/-- The algebraic closure of the rational function field in four variables over `Ω`.-/
abbrev FreshAmbient (Ω : Type*) [Field Ω] : Type _ :=
  AlgebraicClosure (FractionRing (MvPolynomial (Fin 4) Ω))

/-- `FreshAmbient Ω` has transcendence degree at least four over every subfield `k` of `Ω`: the
four variables stay algebraically independent.
@isnad1 id=le.0h2v.s8.f32bdb8c9d17 from=translated src=- shape=41fda58b vocab=5d6ea845
-/
theorem four_le_trdeg_freshAmbient (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] :
    (4 : Cardinal) ≤ Algebra.trdeg k (FreshAmbient Ω) := by
  have hinj : Function.Injective
      (IsScalarTower.toAlgHom Ω (MvPolynomial (Fin 4) Ω) (FreshAmbient Ω)) := by
    change Function.Injective (algebraMap (MvPolynomial (Fin 4) Ω) (FreshAmbient Ω))
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 4) Ω)
      (FractionRing (MvPolynomial (Fin 4) Ω)) (FreshAmbient Ω)]
    exact (algebraMap (FractionRing (MvPolynomial (Fin 4) Ω)) (FreshAmbient Ω)).injective.comp
      (IsFractionRing.injective _ _)
  have hX := ((MvPolynomial.algebraicIndependent_X (Fin 4) Ω).map' hinj).restrictScalars
    (R := k) (algebraMap k Ω).injective
  simpa using hX.lift_cardinalMk_le_trdeg

end AclGeom
