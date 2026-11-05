/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkGenericColimit
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.AlgEquivDescent
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.ScalarExtension
import Tengoku.Seed.Algebra.Algebra.Equiv
import Tengoku.Seed.Algebra.Category.Ring.Under.Basic
import Tengoku.Seed.AlgebraicGeometry.AffineScheme
import Tengoku.Seed.AlgebraicGeometry.GammaSpecAdjunction
import Tengoku.Seed.CategoryTheory.Comma.Over.Basic
import Tengoku.Seed.CategoryTheory.Filtered.FinallySmall
import Tengoku.Seed.CategoryTheory.Sites.Point.Basic
import Tengoku.Seed.RingTheory.FinitePresentation
import Tengoku.Seed.RingTheory.FiniteType
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.RingTheory.TensorProduct.Maps
import Tengoku.Seed.RingTheory.TensorProduct.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict generic equivalences on actual pointed affine neighborhoods

The real generic-neighborhood algebras retain their existing `Under K` scalar
maps. Compactness over K first supplies an actual pointed neighborhood. A
geometric affine refinement then extends that equivalence along its actual
section map. Both forward and inverse squares remain the literal generic
germ squares. No finite presentation of K over R is required.

This is a prerequisite for [Stacks, Tag 0BSM](https://stacks.math.columbia.edu/tag/0BSM). The separate
principal-localization model construction is not used in this route.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

section Neighborhood

variable (R : Type u) [CommRing R]

/-- The actual section algebra of an étale neighborhood of `Spec R`, with
its structure map recorded as an object under R.-/
def geometricNeighborhoodAlgebra (W : (Spec (CommRingCat.of R)).Etale) :
    Under (CommRingCat.of R) :=
  Under.mk ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop)

/-- Pullback of sections along an actual morphism of étale neighborhoods.-/
def geometricNeighborhoodAlgebraMap
    {W V : (Spec (CommRingCat.of R)).Etale} (j : V ⟶ W) :
    geometricNeighborhoodAlgebra R W ⟶ geometricNeighborhoodAlgebra R V :=
  Under.homMk j.left.appTop (by
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop) ≫
      j.left.appTop = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop
    rw [Category.assoc, ← Scheme.Hom.comp_appTop]
    have hj : j.left ≫ (show W.left ⟶ Spec (CommRingCat.of R) from W.hom) =
        (show V.left ⟶ Spec (CommRingCat.of R) from V.hom) := j.w
    exact congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) hj)

/-- The actual generic fiber of the section algebra, with its one existing
K-algebra structure retained in `Under K`.-/
def geometricNeighborhoodGenericAlgebra (W : (Spec (CommRingCat.of R)).Etale) :
    Under (CommRingCat.of (FractionRing R)) :=
  (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).obj
    (geometricNeighborhoodAlgebra R W)

/-- The literal generic section map of an actual neighborhood morphism.-/
def geometricNeighborhoodGenericMap
    {W V : (Spec (CommRingCat.of R)).Etale} (j : V ⟶ W) :
    geometricNeighborhoodGenericAlgebra R W ⟶ geometricNeighborhoodGenericAlgebra R V :=
  (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).map
    (geometricNeighborhoodAlgebraMap R j)

end Neighborhood

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)

end EtaleFundamentalGroups.StrictHenselian
