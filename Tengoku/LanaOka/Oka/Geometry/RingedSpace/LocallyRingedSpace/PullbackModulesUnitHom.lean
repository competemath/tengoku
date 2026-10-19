/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules
import Tengoku.LanaOka.Oka.Algebra.Category.ModuleCat.Sheaf.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pullback of morphisms out of the structure sheaf

Let `f : Y ⟶ X` be a morphism of locally ringed spaces and `H` a sheaf of `𝒪_X`-modules.
Morphisms `𝒪_X ⟶ H` are global sections of `H`, and under the adjunction `f^* ⊣ f_*` the map
`f^* : (𝒪_X ⟶ H) → (f^* 𝒪_X ⟶ f^* H)` becomes composition with the unit `H ⟶ f_* f^* H`. Hence
it is bijective as soon as the unit is bijective on global sections
(`AlgebraicGeometry.LocallyRingedSpace.Hom.bijective_pullbackModules_map_unit`).
-/

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

/-- Composition with `φ : M ⟶ N` is bijective on morphisms out of the structure sheaf if `φ` is
bijective on global sections. -/
lemma bijective_comp_of_bijective_app_top {M N : SheafOfModules.{u} X.ringSheaf} (φ : M ⟶ N)
    (h : Function.Bijective (φ.val.app (op ⊤))) :
    Function.Bijective (fun g : SheafOfModules.unit X.ringSheaf ⟶ M ↦ g ≫ φ) := by
  let hT : IsTerminal (⊤ : Opens X.toPresheafedSpace) := isTerminalTop
  let e (P : SheafOfModules.{u} X.ringSheaf) : P.sections ≃ P.val.obj (op ⊤) :=
    { toFun s := PresheafOfModules.sections.eval s (op ⊤)
      invFun b := SheafOfModules.sectionOfTerminal hT P b
      left_inv s := SheafOfModules.sectionOfTerminal_eval hT P s
      right_inv b := by
        change PresheafOfModules.sections.eval (SheafOfModules.sectionOfTerminal hT P b)
          (op ⊤) = b
        rw [SheafOfModules.sectionOfTerminal_val]
        rw [show hT.from ⊤ = 𝟙 _ from hT.hom_ext _ _, op_id, P.val.map_id]
        rfl }
  have hs : SheafOfModules.sectionsMap φ = (e N).symm ∘ φ.val.app (op ⊤) ∘ e M := by
    funext s
    conv_lhs => rw [← SheafOfModules.sectionOfTerminal_eval hT M s]
    exact SheafOfModules.sectionsMap_sectionOfTerminal hT φ _
  have hc : (fun g : SheafOfModules.unit X.ringSheaf ⟶ M ↦ g ≫ φ) =
      N.unitHomEquiv.symm ∘ SheafOfModules.sectionsMap φ ∘ M.unitHomEquiv := by
    funext g
    apply N.unitHomEquiv.injective
    simp [SheafOfModules.unitHomEquiv_comp_apply]
  rw [hc, hs]
  exact N.unitHomEquiv.symm.bijective.comp
    (((e N).symm.bijective.comp (h.comp (e M).bijective)).comp M.unitHomEquiv.bijective)

end AlgebraicGeometry.LocallyRingedSpace
