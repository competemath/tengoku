import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SL2Elementary
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups
import Tengoku.Seed.NumberTheory.Modular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_closure_elemSet_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_closure_elemSet_eq_top

set_option autoImplicit false

open Matrix MatrixGroups Subgroup ModularCurve

/--
@isnad1 id=eq.0h1v.s7.0cf025ab54f4 from=translated src=- shape=2cf782c4 vocab=96777411
-/
theorem solution (N : ℕ) [NeZero N] :
    Subgroup.closure (ModularCurve.elemSet (ZMod N)) = ⊤ := by
  set φ : SL(2, ℤ) →* SL(2, ZMod N) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) with hφ
  have hT : φ ModularGroup.T = upperElem (1 : ZMod N) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hφ, ModularGroup.coe_T]
  have hS : φ ModularGroup.S =
      upperElem (-1 : ZMod N) * lowerElem 1 * upperElem (-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hφ, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hsurj : Function.Surjective φ :=
    ModularCurve.surjective_specialLinearGroup_map_zmod N
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective φ hsurj,
    ← SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure]
  refine (closure_le _).mpr ?_
  rintro x ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl
  · rw [hS]
    exact mul_mem (mul_mem (upperElem_mem_closure_elemSet _)
      (lowerElem_mem_closure_elemSet _)) (upperElem_mem_closure_elemSet _)
  · rw [hT]
    exact upperElem_mem_closure_elemSet _
