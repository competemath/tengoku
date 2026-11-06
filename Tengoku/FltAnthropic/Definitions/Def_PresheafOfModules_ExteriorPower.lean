import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory
namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

section map
variable {X Y : Cᵒᵖ} (f : X ⟶ Y)

@[reducible] noncomputable def moduleAlong (R : Cᵒᵖ ⥤ CommRingCat.{u}) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (N : Type u) [AddCommGroup N] [Module (R.obj Y) N] : Module (R.obj X) N :=
  Module.compHom N (R.map f).hom

noncomputable def mapAlong :
    letI := moduleAlong R f (M.obj Y)
    M.obj X →ₗ[R.obj X] M.obj Y :=
  letI := moduleAlong R f (M.obj Y)
  { toFun := fun x => (M.map f x : M.obj Y)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => M.map_smul f r x }

end map

end ExteriorPower

end PresheafOfModules

namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

end ExteriorPower

end PresheafOfModules
