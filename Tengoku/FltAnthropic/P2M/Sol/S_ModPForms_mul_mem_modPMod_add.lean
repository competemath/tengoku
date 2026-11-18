import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_mul_mem_modPMod_add.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_mul_mem_modPMod_add

set_option autoImplicit false

open scoped MatrixGroups

namespace FltWs24
namespace ModPMul

/--
@isnad1 id=mem.0h1v.s7.cdd8bd13907c from=translated src=- shape=fab0867b vocab=8624f481
-/
theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]

/--
@isnad1 id=mem.0h1v.s7.42dd5cae402a from=translated src=- shape=eaec2ebd vocab=fbf1a2fe
-/
theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

/--
@isnad1 id=and.2h10v.s9.8733633090e6 from=translated src=- shape=4beb3733 vocab=267c5f63
-/
theorem qCoeff_mul_of_intCast {N : ℕ} {a b : ℤ} {F : Type} [Field F]
    {G₁ G₂ : Type*} [FunLike G₁ UpperHalfPlane ℂ] [FunLike G₂ UpperHalfPlane ℂ]
    (f : G₁) [ModularFormClass G₁ (CongruenceSubgroup.Gamma0 N) a]
    (g : G₂) [ModularFormClass G₂ (CongruenceSubgroup.Gamma0 N) b]
    (c d : ℕ → ℤ) (hc : ∀ n, ModularFormClass.qCoeff f n = (c n : ℂ))
    (hd : ∀ n, ModularFormClass.qCoeff g n = (d n : ℂ)) :
    (∀ n, ModularFormClass.qCoeff (⇑f * ⇑g) n = ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2 : ℤ) : ℂ)) ∧
      (PowerSeries.mk fun n => ((c n : ℤ) : F)) * (PowerSeries.mk fun n => ((d n : ℤ) : F)) =
        PowerSeries.mk fun n => (((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2 : ℤ) : ℤ) : F) := by
  refine ⟨fun n => ?_, ?_⟩
  · unfold ModularFormClass.qCoeff at hc hd ⊢
    rw [ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods_Gamma0 N) f g, PowerSeries.coeff_mul]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by rw [hc, hd]
  · ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Int.cast_sum, Int.cast_mul]

end FltWs24.ModPMul

open FltWs24.ModPMul in
/--
@isnad1 id=mem.2h6v.s9.c37c37c4871f from=translated src=- shape=46dd6bbc vocab=15d45cad
-/
theorem solution (N : ℕ) (a b : ℤ) (F : Type) [Field F]
    (φ ψ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N a F) (hψ : ψ ∈ ModPForms.modPMod N b F) :
    φ * ψ ∈ ModPForms.modPMod N (a + b) F := by
  unfold ModPForms.modPMod at hφ hψ ⊢
  refine Submodule.mul_le.mp ?_ φ hφ ψ hψ
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨x, ⟨f, c, hc, rfl⟩, y, ⟨g, d, hd, rfl⟩, rfl⟩
  obtain ⟨he, hprod⟩ := qCoeff_mul_of_intCast (F := F) f g c d hc hd
  refine Submodule.subset_span ⟨f.mul g, _, fun n => ?_, hprod⟩
  rw [ModularForm.coe_mul]
  exact he n
