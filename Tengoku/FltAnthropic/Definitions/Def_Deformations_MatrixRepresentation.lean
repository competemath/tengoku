import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace Deformation

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

noncomputable def matrixRepresentation (ρ : G →* GL n k) : Representation k G (n → k) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

/--
@isnad1 id=eq.0h5v.s10.2e5acfff8306 from=translated src=- shape=28ac959d vocab=b420fa71
-/
@[simp]
lemma matrixRepresentation_apply (ρ : G →* GL n k) (g : G) :
    matrixRepresentation ρ g = Matrix.mulVecLin (ρ g).val :=
  Matrix.GeneralLinearGroup.coe_toLin _

end Deformation
