import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul
set_option autoImplicit false

open scoped _root_.MatrixGroups _root_.ModularForm _root_.Pointwise
open UpperHalfPlane

noncomputable section

namespace ModularForm
export _root_.ModularForm (translate holo' slash_def ext IsGLPos.smul_apply smul_apply bdd_at_cusps' coe_translate)
namespace LevelTwoDegeneracy
open _root_.ModularForm

def restrict {k : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (F : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := F
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn F γ (h hγ)
  holo' := F.holo'
  bdd_at_cusps' hc := F.bdd_at_cusps' (hc.mono h)

def gTwo : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(2 : ℝ), 0; 0, 1] (by norm_num [Matrix.det_fin_two_of])

end ModularForm.LevelTwoDegeneracy
open scoped _root_.P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm _root_.P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm.LevelTwoDegeneracy
open scoped _root_.P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm

end
open scoped _root_.P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm _root_.P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm.LevelTwoDegeneracy
