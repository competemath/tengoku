/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.AlgebraicGeometry.OrderOfVanishing
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.OrderOfVanishingIso

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Order of vanishing along a morphism with isomorphic stalk maps (route D7, part b)

If `φ : X ⟶ Y` is a morphism of integral locally Noetherian schemes whose stalk maps are all
isomorphisms and which sends the generic point to the generic point, then the induced
isomorphism `K(Y) ≃ K(X)` is compatible with orders of vanishing: `ord (φ^* q) x = ord q (φ x)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Chow.D7

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (φ : X ⟶ Y)
  [∀ x, IsIso (φ.stalkMap x)] (hgen : φ (genericPoint X) = genericPoint Y)

/-- The function-field isomorphism of a morphism with isomorphic stalks.-/
def ffIso : Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr (.of_eq hgen.symm) ≪≫ asIso (φ.stalkMap (genericPoint X))

include hgen in
/--
@isnad1 id=eq.1h5v.s13.e4d0424461fa from=translated src=- shape=4ffe71a4 vocab=25c83b41
-/
theorem ffIso_algebraMap (x : X) (r : Y.presheaf.stalk (φ x)) :
    (ffIso φ hgen).commRingCatIsoToRingEquiv
        (algebraMap (Y.presheaf.stalk (φ x)) Y.functionField r) =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((asIso (φ.stalkMap x)).commRingCatIsoToRingEquiv r) := by
  let hX : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let hY : genericPoint Y ⤳ φ x := (genericPoint_spec Y).specializes trivial
  let hη : φ (genericPoint X) ⤳ genericPoint Y := specializes_of_eq hgen
  have htransport :
      (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom
          (Y.presheaf.stalkSpecializes hY r) =
        Y.presheaf.stalkSpecializes (hX.map φ.continuous) r := by
    change (Y.presheaf.stalkSpecializes hη)
        (Y.presheaf.stalkSpecializes hY r) =
      Y.presheaf.stalkSpecializes (hX.map φ.continuous) r
    rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  change (φ.stalkMap (genericPoint X)).hom
      ((Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom
        (Y.presheaf.stalkSpecializes hY r)) =
    X.presheaf.stalkSpecializes hX ((φ.stalkMap x).hom r)
  rw [htransport]
  exact φ.stalkSpecializes_stalkMap_apply (genericPoint X) x hX r

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

omit [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
/--
@isnad1 id=eq.0h4v.s8.fcdc226ec822 from=translated src=- shape=eb3d5ea9 vocab=7f71574f
-/
theorem coheight_map_of_isIso_stalkMap (x : X) : coheight (φ x) = coheight x := by
  have h1 := ringKrullDim_stalk_eq_coheight (X := X) x
  have h2 := ringKrullDim_stalk_eq_coheight (X := Y) (φ x)
  have h3 : ringKrullDim (Y.presheaf.stalk (φ x)) = ringKrullDim (X.presheaf.stalk x) :=
    ringKrullDim_eq_of_ringEquiv (asIso (φ.stalkMap x)).commRingCatIsoToRingEquiv
  rw [h3, h1] at h2
  exact_mod_cast h2.symm

end AlgebraicGeometry.Chow.D7
