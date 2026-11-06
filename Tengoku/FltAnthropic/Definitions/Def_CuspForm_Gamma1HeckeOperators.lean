import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace CuspForm.Gamma1Hecke

open Matrix.SpecialLinearGroup UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm OnePoint Manifold

/--
@isnad1 id=eq.0h3v.s9.5be642610faa from=translated src=- shape=531976e2 vocab=c63d16f2
-/
theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

attribute [local simp] mapGL_apply

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

end commutation

section reindex

variable {p : ℕ} [NeZero p]

end reindex

section reps

variable {p : ℕ}

variable {N : ℕ}

end reps

section heckeT

variable {p : ℕ} [Fact p.Prime]

variable {N : ℕ} (k : ℤ)

end heckeT

end CuspForm.Gamma1Hecke

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace CuspForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Lifts

variable (M : ℕ)

variable {M}

end Lifts

section Diamond

variable (M : ℕ) (k : ℤ)

variable {M k}

end Diamond

section Hecke

variable (k : ℤ) {M ℓ : ℕ}

end Hecke

end CuspForm

end
