import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms
import Tengoku.FltAnthropic.Theorems.Thm_CuspForm_qCoeffLinear_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_modPMod_eq_bot_of_neg.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_modPMod_eq_bot_of_neg

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=eq.1h3v.s7.c17414f83d01 from=translated src=- shape=06bd905d vocab=a5bb5523
-/
theorem solution (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) (F : Type) [Field F] :
    ModPForms.modPMod N k F = ⊥ := by
  unfold ModPForms.modPMod
  rw [Submodule.span_eq_bot]
  rintro φ ⟨f, a, ha, rfl⟩
  have hf : f = 0 := ModularForm.isZero_of_neg_weight hk f
  have h0 : ∀ n, ModularFormClass.qCoeff (f : UpperHalfPlane → ℂ) n = 0 := by
    intro n
    have e : (f : UpperHalfPlane → ℂ) = ((0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) : UpperHalfPlane → ℂ) := by
      rw [hf, FunLike.coe_zero, FunLike.coe_zero]
    rw [e, ← CuspForm.qCoeffLinear_apply, map_zero]
  have han : ∀ n, a n = 0 := fun n => by
    have h := ha n
    rw [h0 n] at h
    exact_mod_cast h.symm
  ext n
  simp [PowerSeries.coeff_mk, han]
