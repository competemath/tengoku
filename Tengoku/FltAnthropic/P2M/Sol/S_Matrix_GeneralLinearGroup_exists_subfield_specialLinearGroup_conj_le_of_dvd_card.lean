import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SL2Elementary
import Tengoku.FltAnthropic.Theorems.Thm_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card

set_option autoImplicit false

open Matrix MatrixGroups

namespace P2mDicksonGL2

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K

/--
@isnad1 id=eq.0h4v.s8.180d897c2eb3 from=translated src=- shape=be158ace vocab=5fc86b63
-/
lemma mulVec_fin_two (M : 𝕄) (x y : K) :
    M *ᵥ ![x, y] = ![M 0 0 * x + M 0 1 * y, M 1 0 * x + M 1 1 * y] := by
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

open ModularCurve

section SL2

def diagElem (a : K) (ha : a ≠ 0) : SL(2, K) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha]⟩

end SL2

section RationalLines

variable {p : ℕ} [Fact p.Prime] [CharP K p]

end RationalLines

section Rational

end Rational

section Setup

variable {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "GL₂" => GL (Fin 2) K

end Setup

section Assembly

variable {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "GL₂" => GL (Fin 2) K

end Assembly

end P2mDicksonGL2
open scoped _root_.P2MW.S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card.P2mDicksonGL2
