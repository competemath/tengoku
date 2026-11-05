/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Inertia.IntegralClosureGaloisAction
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Inertia.TrivialNormalizationInertiaEtale
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteResidueGeometricPoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fixed geometric-point inertia implies étaleness over a DVR

Every prime over the closed point is represented in the fixed algebraic
closure of the base residue field. The actual affine normalization comparison
then turns geometric fixed-point triviality into the ideal inertia condition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The actual affine normalization isomorphism commutes with its base map.
@isnad1 id=eq.0h2v.s9.9a36f4de9600 from=translated src=- shape=bf71f72a vocab=9a05f562
-/
@[reassoc]
theorem specNormalizationIso_hom_base
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    (specNormalizationIso R B).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R B))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization := by
  apply spec_toNormalization_hom_ext R B
  rw [← Category.assoc, toNormalization_specNormalizationIso_hom,
    Scheme.Hom.toNormalization_fromNormalization, ← Spec.map_comp]
  rfl

end EtaleFundamentalGroups.Inertia
