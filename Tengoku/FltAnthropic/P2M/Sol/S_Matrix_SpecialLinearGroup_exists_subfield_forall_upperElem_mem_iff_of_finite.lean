import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SL2Elementary
import Tengoku.FltAnthropic.Theorems.Thm_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite

set_option autoImplicit false

open Matrix MatrixGroups ModularCurve

namespace P2mDicksonSL2

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K

def diagElem (a : K) (ha : a ≠ 0) : SL(2, K) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha]⟩

section Sylows

variable {p : ℕ} [Fact p.Prime] [CharP K p]

variable (G : Subgroup SL(2, K))

variable {G}

end Sylows

section Orbit

end Orbit

section Main

variable {p : ℕ} [Fact p.Prime] [CharP K p]

end Main

end P2mDicksonSL2
