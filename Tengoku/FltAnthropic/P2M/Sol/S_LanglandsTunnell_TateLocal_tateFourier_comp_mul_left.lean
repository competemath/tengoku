import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left

set_option autoImplicit false

open MeasureTheory

namespace LanglandsTunnell
namespace TateLocal
export _root_.LanglandsTunnell.TateLocal (modulus modulus_of_ne_zero tateFourier)
namespace FourierDilation
open _root_.LanglandsTunnell.TateLocal open _root_.LanglandsTunnell

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]
  [MeasurableSpace A] [BorelSpace A]

private theorem domSMul_eq_distribHaarChar_smul (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular]
    (g : G) : DomMulAct.mk g • μ = distribHaarChar A g • μ :=
  (Measure.isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk g • μ) μ).trans
    (by rw [addHaarScalarFactor_smul_eq_distribHaarChar])

private theorem integral_smul_comp (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (g : G)
    (F : A → ℂ) :
    ∫ x, F (g • x) ∂μ = ((distribHaarChar A g⁻¹ : ℝ) : ℂ) * ∫ x, F x ∂μ := by
  have h : ∫ x, F x ∂(DomMulAct.mk g⁻¹ • μ) = ∫ x, F (g • x) ∂μ := by
    rw [integral_domSMul]
    simp only [Equiv.symm_apply_apply, inv_inv]
  rw [domSMul_eq_distribHaarChar_smul μ g⁻¹, integral_smul_nnreal_measure] at h
  exact h.symm

end LanglandsTunnell.TateLocal.FourierDilation

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left.LanglandsTunnell.TateLocal in
theorem solution (K : Type*) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (ψ : AddChar K ℂ) (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (f : K → ℂ) (a : K)
    (ha : a ≠ 0) (y : K) :
    tateFourier ψ μ (fun x => f (a * x)) y
      = ((modulus a : ℝ) : ℂ)⁻¹ * tateFourier ψ μ f (a⁻¹ * y) := by
  have hpt : ∀ x : K, a * x * (a⁻¹ * y) = x * y := fun x => by
    calc a * x * (a⁻¹ * y) = a * a⁻¹ * (x * y) := by ring
      _ = x * y := by rw [mul_inv_cancel₀ ha, one_mul]

  have key : ∫ x, f (a * x) * ψ (a * x * (a⁻¹ * y)) ∂μ
      = ((distribHaarChar K (Units.mk0 a ha)⁻¹ : ℝ) : ℂ) * ∫ x, f x * ψ (x * (a⁻¹ * y)) ∂μ :=
    FourierDilation.integral_smul_comp μ (Units.mk0 a ha) (fun x => f x * ψ (x * (a⁻¹ * y)))
  simp only [hpt] at key
  rw [map_inv, NNReal.coe_inv, Complex.ofReal_inv] at key
  unfold tateFourier
  rw [modulus_of_ne_zero ha]
  exact key
