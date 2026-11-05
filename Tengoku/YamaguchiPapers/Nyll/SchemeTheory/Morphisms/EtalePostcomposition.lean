/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.AlgebraicGeometry.Geometrically.Reduced
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FinitePresentation
import Tengoku.Seed.CategoryTheory.Limits.Shapes.Diagonal
import Tengoku.Seed.CategoryTheory.MorphismProperty.Limits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cancelling an etale second morphism

If the second map of a factorization is etale, its graph is an open
immersion into the base change of the composite. Flatness, local finite
presentation, and geometric reducedness of the composite therefore hold
for the first map as well. The graph and its open immersion are constructed
from the actual diagonal; no graph or comparison is supplied as input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- An open subscheme of a geometrically reduced scheme remains geometrically
reduced over the same base.
@isnad1 id=geometri.0h5v.s5.55073b4a0c42 from=translated src=- shape=aa4db468 vocab=1318f591
-/
lemma GeometricallyReduced.comp_of_isOpenImmersion
    {U X S : Scheme.{u}} (i : U ⟶ X) (f : X ⟶ S)
    [IsOpenImmersion i] [GeometricallyReduced f] :
    GeometricallyReduced (i ≫ f) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ y
  let j : pullback (i ≫ f) y ⟶ pullback f y :=
    pullback.map (i ≫ f) y f y i (𝟙 _) (𝟙 _)
      (Category.comp_id (i ≫ f))
      ((Category.comp_id y).trans (Category.id_comp y).symm)
  have : IsOpenImmersion j :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (f := i ≫ f) (g := y) (f' := f) (g' := y)
      (inferInstance : IsOpenImmersion i)
      (inferInstance : IsOpenImmersion (𝟙 (Spec (CommRingCat.of K))))
      rfl (Category.id_comp y).symm
  have : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced (f := f) y
      (pullback.fst f y) (pullback.snd f y) (IsPullback.of_hasPullback f y)
  exact isReduced_of_isOpenImmersion j

/-- Flatness, local finite presentation, and geometric reducedness descend
through etale postcomposition by expressing the first map as its open graph
followed by the base change of the composite.
@isnad1 id=and.0h5v.s6.130fa5cdb1cf from=translated src=- shape=67f65809 vocab=98f695f5
-/
lemma flat_finitePresentation_geometricallyReduced_of_comp_etale
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Etale g] [Flat (f ≫ g)] [LocallyOfFinitePresentation (f ≫ g)]
    [GeometricallyReduced (f ≫ g)] :
    Flat f ∧ LocallyOfFinitePresentation f ∧ GeometricallyReduced f := by
  let graph : X ⟶ pullback (f ≫ g) g :=
    pullback.lift (𝟙 X) f ((Category.id_comp (f ≫ g)).trans rfl)
  have : IsOpenImmersion graph :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback f g)
      (inferInstance : IsOpenImmersion (pullback.diagonal g))
  have hFactor : graph ≫ pullback.snd (f ≫ g) g = f :=
    pullback.lift_snd _ _ _
  have hFlat : Flat (graph ≫ pullback.snd (f ≫ g) g) := inferInstance
  have hPresentation : LocallyOfFinitePresentation
      (graph ≫ pullback.snd (f ≫ g) g) := inferInstance
  have hReduced : GeometricallyReduced (graph ≫ pullback.snd (f ≫ g) g) :=
    GeometricallyReduced.comp_of_isOpenImmersion graph (pullback.snd (f ≫ g) g)
  exact ⟨hFactor ▸ hFlat, hFactor ▸ hPresentation, hFactor ▸ hReduced⟩

end AlgebraicGeometry
