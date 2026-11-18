import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_modPMod_le_modPMod_of_dvd.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_modPMod_le_modPMod_of_dvd
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace ModPForms
export _root_.ModPForms (modPCusp modPMod)
namespace LevelIncl
open _root_.ModPForms
open scoped MatrixGroups

variable {M N : ℕ} (k : ℤ)

/--
@isnad1 id=le.1h2v.s7.48cc5f78829a from=translated src=- shape=01686ef7 vocab=ee1e3f6e
-/
theorem Gamma0_le_of_dvd (hMN : M ∣ N) :
    CongruenceSubgroup.Gamma0 N ≤ CongruenceSubgroup.Gamma0 M := fun A hA => by
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  have h := congrArg (ZMod.castHom hMN (ZMod M)) hA
  rwa [map_intCast, map_zero] at h

/--
@isnad1 id=le.1h2v.s9.6eb5acf8bc5e from=translated src=- shape=b4ab2b16 vocab=274d8678
-/
theorem Gamma0GL_le_of_dvd (hMN : M ∣ N) :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma0_le_of_dvd hMN)

def restrictCusp (hMN : M ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k where
  toFun := ⇑f
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (Gamma0GL_le_of_dvd hMN hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps f (hc.mono (Gamma0GL_le_of_dvd hMN))

def restrictMod (hMN : M ∣ N) (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k where
  toFun := ⇑f
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (Gamma0GL_le_of_dvd hMN hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := fun hc => ModularFormClass.bdd_at_cusps f (hc.mono (Gamma0GL_le_of_dvd hMN))

/--
@isnad1 id=eq.1h4v.s9.d12b009bb736 from=translated src=- shape=1d9e27bf vocab=f74c846d
-/
@[scoped simp] theorem coe_restrictMod (hMN : M ∣ N) (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) :
    ⇑(restrictMod k hMN f) = ⇑f := rfl

/--
@isnad1 id=le.1h4v.s7.0367b1f17e5c from=translated src=- shape=d22a58dd vocab=eca1c861
-/
theorem modPMod_le_modPMod_of_dvd (M N : ℕ) (hMN : M ∣ N) (k : ℤ) (F : Type) [Field F] :
    ModPForms.modPMod M k F ≤ ModPForms.modPMod N k F := by
  refine Submodule.span_mono ?_
  rintro φ ⟨f, a, ha, rfl⟩
  exact ⟨restrictMod k hMN f, a, fun n => by rw [coe_restrictMod]; exact ha n, rfl⟩

end ModPForms.LevelIncl
open scoped _root_.P2MW.S_ModPForms_modPMod_le_modPMod_of_dvd.ModPForms _root_.P2MW.S_ModPForms_modPMod_le_modPMod_of_dvd.ModPForms.LevelIncl
open scoped _root_.P2MW.S_ModPForms_modPMod_le_modPMod_of_dvd.ModPForms

/--
@isnad1 id=le.1h4v.s7.0367b1f17e5c from=translated src=- shape=d22a58dd vocab=eca1c861
-/
theorem solution (M N : ℕ) (hMN : M ∣ N) (k : ℤ) (F : Type) [Field F] :
    ModPForms.modPMod M k F ≤ ModPForms.modPMod N k F :=
  ModPForms.LevelIncl.modPMod_le_modPMod_of_dvd M N hMN k F
