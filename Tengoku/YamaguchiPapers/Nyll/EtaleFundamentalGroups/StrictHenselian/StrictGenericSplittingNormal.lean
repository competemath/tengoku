/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAffineGenericDescent
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.AffineNeighborhoodFaithfullyFlat
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.FieldExtensions.GenericTensorSplit
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Etale.IntegralClosureEtaleOfSplit
import Tengoku.Seed.Algebra.Algebra.Defs
import Tengoku.Seed.Algebra.Category.Ring.Under.Basic
import Tengoku.Seed.AlgebraicGeometry.AffineScheme
import Tengoku.Seed.AlgebraicGeometry.GammaSpecAdjunction
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict generic splitting and normalization over a normal local domain

A splitting over the actual strict generic field descends to an actual pointed
affine étale neighborhood. Its actual section algebra is faithfully flat.
The concrete tensor cancellation and commutation comparison then supplies the
generic-fiber splitting used by normal-localization and integral-closure descent.
No finite presentation of the original fraction field over its base is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Restore the original scalar dictionary after the canonical Under
construction. The scalar-map identity, including its induced tensor action,
is supplied by `toAlgebra_algebraMap`.-/
private def mkUnderTensorSplit
    {K : CommRingCat.{u}} {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (ι : Type u)
    (e : ((CommRingCat.mkUnder K A) ⊗[K] B) ≃ₐ[CommRingCat.mkUnder K A]
      (ι → CommRingCat.mkUnder K A)) :
    (A ⊗[K] B) ≃ₐ[A] (ι → A) := by
  change (letI : Algebra K A := (algebraMap K A).toAlgebra
    (A ⊗[K] B) ≃ₐ[A] (ι → A)) at e
  exact Eq.mp (congrArg (fun scalar : Algebra K A =>
    letI : Algebra K A := scalar
    (A ⊗[K] B) ≃ₐ[A] (ι → A)) (toAlgebra_algebraMap (R := K) (S := A))) e

end EtaleFundamentalGroups.StrictHenselian
