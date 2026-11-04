/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Preimmersion
import Tengoku.Seed.AlgebraicGeometry.Stalk
import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier
import Tengoku.Seed.AlgebraicGeometry.Properties
import Tengoku.Seed.AlgebraicGeometry.Noetherian
import Tengoku.Seed.RingTheory.Flat.Localization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The generic fibre `W ×_Y Spec K(Y)` as an integral scheme (route D7, part a)

For a dominant morphism `h : W ⟶ Y` of integral schemes, the generic fibre
`GF h = W ×_Y Spec K(Y)` is an integral scheme, and the projection `g' : GF h ⟶ W` has
isomorphic stalk maps at every point (it is flat and a preimmersion).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Chow.D7

/-- A flat preimmersion has isomorphic stalk maps.
@isnad1 id=isiso.0h4v.s8.0900fd813358 from=translated src=- shape=b48dd0f3 vocab=9d4e87be
-/
theorem isIso_stalkMap_of_flat_of_preimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsPreimmersion f] (x : X) : IsIso (f.stalkMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, f.stalkMap_surjective x⟩
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

section

variable {W Y : Scheme.{u}} [IsIntegral W] [IsIntegral Y] (h : W ⟶ Y)

/-- `Spec K(Y)`.-/
abbrev SK (Y : Scheme.{u}) [IsIntegral Y] : Scheme.{u} := Spec (Y.presheaf.stalk (genericPoint Y))

/-- The canonical morphism `Spec K(Y) ⟶ Y`.-/
abbrev gS (Y : Scheme.{u}) [IsIntegral Y] : SK Y ⟶ Y := Y.fromSpecStalk (genericPoint Y)

/-- The generic fibre `W ×_Y Spec K(Y)`.-/
abbrev GF (h : W ⟶ Y) : Scheme.{u} := pullback h (gS Y)

/-- The projection of the generic fibre to `W`.-/
abbrev gF (h : W ⟶ Y) : GF h ⟶ W := pullback.fst h (gS Y)

/-- The structure morphism of the generic fibre.-/
abbrev fF (h : W ⟶ Y) : GF h ⟶ SK Y := pullback.snd h (gS Y)

/--
@isnad1 id=eq.0h1v.s8.0069db175f2b from=translated src=- shape=126a3498 vocab=05018fe3
-/
theorem gS_closedPoint : gS Y (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y))) =
    genericPoint Y := Scheme.fromSpecStalk_closedPoint

/--
@isnad1 id=eq.0h3v.s7.e3ac0f59c913 from=translated src=- shape=54be5bf5 vocab=28308992
-/
theorem genericPoint_map_of_isDominant' [IsDominant h] : h (genericPoint W) = genericPoint Y := by
  have h1 := (genericPoint_spec W).image h.continuous
  rw [Set.image_univ, h.denseRange.closure_range] at h1
  exact h1.eq (genericPoint_spec Y)

/--
@isnad1 id=ex.0h3v.s8.2766dcd11835 from=translated src=- shape=49d472a9 vocab=0f5951ea
-/
theorem exists_point [IsDominant h] :
    ∃ x0 : GF h, gF h x0 = genericPoint W := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := gS Y)
    (genericPoint W) (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)))
    ((genericPoint_map_of_isDominant' h).trans gS_closedPoint.symm)
  exact ⟨z, hz⟩

end

end AlgebraicGeometry.Chow.D7
