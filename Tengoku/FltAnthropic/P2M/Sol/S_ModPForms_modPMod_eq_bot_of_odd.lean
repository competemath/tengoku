import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_modPMod_eq_bot_of_odd.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_modPMod_eq_bot_of_odd
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
namespace ModPForms
export _root_.ModPForms (modPMod)
namespace OddWeight
open _root_.ModPForms
open scoped MatrixGroups

/--
@isnad1 id=mem.0h1v.s9.828119a50823 from=translated src=- shape=1a42b456 vocab=6d52720b
-/
theorem neg_one_mem_Gamma0 (N : ℕ) :
    (-1 : GL (Fin 2) ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  refine ⟨-1, ?_, ?_⟩
  · simp [CongruenceSubgroup.Gamma0_mem]
  · ext i j
    simp [Matrix.SpecialLinearGroup.coe_int_neg]

/--
@isnad1 id=eq.1h3v.s9.eae7f22d5fde from=translated src=- shape=7d4e36f4 vocab=b1d9ab52
-/
theorem modularForm_eq_zero_of_odd (N : ℕ) (k : ℤ) (hk : Odd k)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by
  ext z
  have hf := SlashInvariantForm.slash_action_eqn'' f (neg_one_mem_Gamma0 N) z
  rw [UpperHalfPlane.neg_smul, one_smul, UpperHalfPlane.denom_neg, UpperHalfPlane.denom_one,
    Odd.neg_one_zpow hk] at hf
  have h2 : (2 : ℂ) * f z = 0 := by linear_combination hf
  rw [zero_apply]
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/--
@isnad1 id=eq.0h1v.s4.9e3d1f4150c0 from=translated src=- shape=12c22aa8 vocab=e85eca0f
-/
theorem qCoeff_zero (n : ℕ) : ModularFormClass.qCoeff (0 : UpperHalfPlane → ℂ) n = 0 := by
  show (UpperHalfPlane.qExpansion 1 (0 : UpperHalfPlane → ℂ)).coeff n = 0
  rw [UpperHalfPlane.qExpansion_zero]; simp

/--
@isnad1 id=eq.1h3v.s7.3ef32c6afcf9 from=translated src=- shape=1efb8ffe vocab=ab33d3c6
-/
theorem modPMod_eq_bot_of_odd (N : ℕ) (k : ℤ) (hk : Odd k) (F : Type) [Field F] :
    ModPForms.modPMod N k F = ⊥ := by
  rw [ModPForms.modPMod, Submodule.span_eq_bot]
  rintro φ ⟨f, a, ha, rfl⟩
  have hf : f = 0 := modularForm_eq_zero_of_odd N k hk f
  ext n
  rw [PowerSeries.coeff_mk, map_zero]
  have han : (a n : ℂ) = 0 := by rw [← ha n, hf, FunLike.coe_zero, qCoeff_zero]
  have : a n = 0 := by exact_mod_cast han
  simp [this]

end ModPForms.OddWeight

/--
@isnad1 id=eq.1h3v.s7.3ef32c6afcf9 from=translated src=- shape=1efb8ffe vocab=ab33d3c6
-/
theorem solution (N : ℕ) (k : ℤ) (hk : Odd k) (F : Type) [Field F] :
    ModPForms.modPMod N k F = ⊥ :=
  ModPForms.OddWeight.modPMod_eq_bot_of_odd N k hk F
