import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)

noncomputable def restrictPushforwardOpensIso :
    (Opens.map (g ∣_ W).base ⋙ (g ⁻¹ᵁ W).ι.opensFunctor : W.toScheme.Opens ⥤ X.Opens) ≅
      W.ι.opensFunctor ⋙ Opens.map g.base :=
  NatIso.ofComponents (fun U => eqToIso (image_morphismRestrict_preimage g W U))
    (fun _ => Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.Modules
