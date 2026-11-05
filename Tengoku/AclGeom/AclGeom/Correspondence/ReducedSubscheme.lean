/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Functorial
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reduced induced closed subschemes

For a closed subset `Z` of a scheme `X`, the reduced induced closed subscheme is the subscheme cut
out by the vanishing ideal sheaf of `Z` (Mathlib's `IdealSheafData.vanishingIdeal`). This module
proves three facts about it.

* The kernel of a morphism from a reduced scheme is the vanishing ideal of the closure of its
  range (`ker_eq_vanishingIdeal_of_isReduced`).
* The reduced induced subscheme is reduced (`isReduced_subscheme_vanishingIdeal`), and integral on
  an irreducible closed set (`isIntegral_subscheme_vanishingIdeal`).
* A morphism from a reduced scheme whose range lies in `Z` factors through it
  (`liftToReducedSubscheme`).

The named consumers are the source-generic bridge and the algebraic-subgroup bridge of blueprint
Lemma `curve-coset` for a general group scheme, composed in `curveCoset_of_genericProduct`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the kernel formula, reducedness, integrality and the factorization are proved.
-/

namespace AclGeom

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- The kernel of a morphism from a reduced scheme is the vanishing ideal of the closure of its
range.
@isnad1 id=eq.0h3v.s7.98ed96d29be8 from=translated src=- shape=275fa484 vocab=98afe5eb
-/
theorem ker_eq_vanishingIdeal_of_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range f)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal,
    Closeds.coe_top, Set.image_univ]

/-- The reduced induced closed subscheme on a closed subset is reduced.
@isnad1 id=isreduce.0h2v.s4.11465edb3f18 from=translated src=- shape=fa1dae77 vocab=61feab1b
-/
instance isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have hX : ∀ U : X.affineOpens,
      IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) := by
    intro U
    have : _root_.IsReduced (Γ(X, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact (Ideal.isRadical_iff_quotient_reduced _).mp (PrimeSpectrum.isRadical_vanishingIdeal _)
    exact (affine_isReduced_iff
      (.of (Γ(X, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U))).2 this
  exact @IsReduced.of_openCover _
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover hX

/-- The reduced induced closed subscheme on an irreducible closed subset is integral.
@isnad1 id=isintegr.1h2v.s6.0b9857bbf937 from=translated src=- shape=36db2747 vocab=27d0fe03
-/
theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have hemb := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hirr : IsIrreducible (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) := by
    rw [hrange]
    exact hZ
  have : IrreducibleSpace (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    Subtype.irreducibleSpace hirr
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    hemb.toHomeomorph.irreducibleSpace_iff.2 this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A morphism from a reduced scheme with range in a closed set `Z` factors through the reduced
induced closed subscheme on `Z`.-/
noncomputable def liftToReducedSubscheme {X Y : Scheme.{u}} (Z : Closeds X) (f : Y ⟶ X)
    [IsReduced Y] (hf : Set.range f ⊆ Z) : Y ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  IsClosedImmersion.lift (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι f (by
    rw [Scheme.IdealSheafData.ker_subschemeι, ker_eq_vanishingIdeal_of_isReduced f]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (closure_minimal hf Z.isClosed))

/-- The factorization through the reduced induced subscheme.
@isnad1 id=eq.1h4v.s8.4e807ad6d6a5 from=translated src=- shape=dbffae0e vocab=caa5c289
-/
theorem liftToReducedSubscheme_subschemeι {X Y : Scheme.{u}} (Z : Closeds X) (f : Y ⟶ X)
    [IsReduced Y] (hf : Set.range f ⊆ Z) :
    liftToReducedSubscheme Z f hf ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = f :=
  IsClosedImmersion.lift_fac _ _ _

end AclGeom
