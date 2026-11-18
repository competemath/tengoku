import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_QuatH

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_not_isGalois_fixFld_sylowH.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_not_isGalois_fixFld_sylowH

set_option autoImplicit false

namespace LanglandsTunnell
export _root_.LanglandsTunnell (fixFld sylowH mem_sylowH_iff)
namespace CubicResolventNotGalois
open _root_.LanglandsTunnell

open FLT.ExplicitLift LanglandsTunnell.Lift48

private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private theorem red_eq_redc (z : ℤ√(-2)) : red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [red, redc, Zsqrtd.lift, sub_eq_add_neg]

private theorem map_red_eq_map_redc (m : Mat) : m.map red = m.map redc := by
  ext i j; simp [Matrix.map_apply, red_eq_redc]

private def tU : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  ⟨tbar, !![-1, -1; 1, -1], by decide, by decide⟩

private def sU : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  ⟨sbar, !![0, -1; 1, -1], by decide, by decide⟩

private theorem map_redc_ne_conj :
    ∀ M ∈ P16, M.map redc ≠ ((sU * tU * sU⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  decide

private theorem not_normal_sylowH {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : ¬ (sylowH e).Normal := by
  intro hN
  have ht : e.symm tU ∈ sylowH e := by
    rw [mem_sylowH_iff, MulEquiv.apply_symm_apply]
    refine ⟨Tlift, one_mem_P16.2.1, ?_⟩
    rw [map_red_eq_map_redc]
    decide
  have hc := hN.conj_mem _ ht (e.symm sU)
  rw [mem_sylowH_iff] at hc
  obtain ⟨M, hM, hEq⟩ := hc
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, map_red_eq_map_redc] at hEq
  exact map_redc_ne_conj M hM hEq

end LanglandsTunnell.CubicResolventNotGalois

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_not_isGalois_fixFld_sylowH.LanglandsTunnell in
/--
@isnad1 id=not.0h2v.s9.78990400f336 from=translated src=- shape=48f66897 vocab=a4f4d726
-/
theorem solution {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ¬ IsGalois ℚ ↥(fixFld (sylowH e)) := by
  intro hG
  refine LanglandsTunnell.CubicResolventNotGalois.not_normal_sylowH e ?_
  have h : (fixFld (sylowH e)).fixingSubgroup.Normal :=
    @IsGalois.fixingSubgroup_normal_of_isGalois ℚ L _ _ _ (fixFld (sylowH e)) _ hG
  rwa [show (fixFld (sylowH e)).fixingSubgroup = sylowH e from
    IntermediateField.fixingSubgroup_fixedField (sylowH e)] at h
