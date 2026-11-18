import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchPlace
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchParam
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Deligne
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchEpsilon
import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.Seed.Analysis.SpecialFunctions.PolarCoord
import Tengoku.Seed.Analysis.Complex.Circle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.lean`: wrote out 13 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 6 `p2m_export`, 7 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal

set_option autoImplicit false

section RealZeta

open _root_.MeasureTheory open _root_.Set open _root_.LanglandsTunnell open _root_.LanglandsTunnell.TateLocal open _root_.LanglandsTunnell.ArchPlace
open scoped Real

namespace LanglandsTunnell
export _root_.LanglandsTunnell (signShift)
namespace ArchPlace
export _root_.LanglandsTunnell.ArchPlace (anglePhase complexCharFun complexCharFun_apply complexTestFun complexZeta realSign realCharFun realTestFun realZeta)
open _root_.LanglandsTunnell.ArchPlace open _root_.LanglandsTunnell

private theorem integral_comp_abs_cx {f : ℝ → ℂ} :
    ∫ x, f |x| = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Ioi 0, f |x| = ∫ (x : ℝ) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, mul_zero]

private theorem mellin_gaussian {z : ℂ} (hz : 0 < z.re) :
    mellin (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) z
      = (2 : ℂ)⁻¹ * (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2) := by
  have h1 : (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ))
      = fun t : ℝ => (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ)) (t ^ (2 : ℝ)) := by
    funext t
    have hp : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast t 2]
      norm_num
    rw [hp]
  have h2 := mellin_comp_rpow (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ)) z (2 : ℝ)
  have h3 := mellin_comp_mul_left (fun u : ℝ => (Real.exp (-u) : ℂ)) (z / 2) Real.pi_pos
  have h4 : (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ))
      = fun u : ℝ => (fun v : ℝ => (Real.exp (-v) : ℂ)) (Real.pi * u) := by
    funext u; rfl
  have h5 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2) = Complex.Gamma (z / 2) := by
    have h6 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2)
        = Complex.GammaIntegral (z / 2) := by
      rw [Complex.GammaIntegral_eq_mellin]
    rw [h6, ← Complex.Gamma_eq_integral (by simpa using hz)]
  have hcast : z / ((2 : ℝ) : ℂ) = z / 2 := by norm_num
  rw [h1, h2, hcast, h4, h3, h5]
  rw [Complex.real_smul, smul_eq_mul]
  have habs : |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [habs]
  push_cast
  ring

private theorem realCharFun_val (u : ℂ) (a : ZMod 2) (x : ℝˣ) :
    ((realCharFun u a x : ℂˣ) : ℂ)
      = ((‖(x : ℝ)‖ : ℝ) : ℂ) ^ u * (((x : ℝ) : ℂ) / ((‖(x : ℝ)‖ : ℝ) : ℂ)) ^ (a.val : ℕ) := by
  simp only [realCharFun, realSign, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_mk0]

private theorem pow_mul_sign_pow (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x : ℂ) ^ n * ((x : ℂ) / ((‖x‖ : ℝ) : ℂ)) ^ n = ((|x| : ℝ) : ℂ) ^ n := by
  rw [← mul_pow]
  congr 1
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [Real.norm_eq_abs, abs_of_neg hneg]
    push_cast
    rw [div_neg, div_self hxC]
    ring
  · rw [Real.norm_eq_abs, abs_of_pos hpos]
    rw [div_self hxC]
    ring

private theorem signShift_eq_val (a : ZMod 2) : signShift a = (a.val : ℂ) := by
  by_cases h : a = 0
  · subst h
    unfold signShift
    rw [ite_eq_left rfl, ZMod.val_zero, Nat.cast_zero]
  · have h01 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    have h1 : a = 1 := (h01 a).resolve_left h
    subst h1
    unfold signShift
    rw [ite_eq_right (by decide : (1 : ZMod 2) ≠ 0)]
    have hv : ((1 : ZMod 2)).val = 1 := by decide
    rw [hv, Nat.cast_one]

private theorem realZeta_realTestFun_realCharFun_eq_GammaReal (u : ℂ) (a : ZMod 2) (s : ℂ)
    (hs : 0 < (s + (u + signShift a)).re) :
    realZeta volume (realTestFun a) (realCharFun u a) s = Complex.Gammaℝ (s + (u + signShift a)) := by
  set z : ℂ := s + (u + signShift a) with hzdef
  have hav : (a.val : ℂ) = signShift a := (signShift_eq_val a).symm
  have hpt : ∀ x : ℝ, x ≠ 0 →
      realTestFun a x * charExt (realCharFun u a) x * ((‖x‖ : ℂ) ^ (s - 1))
        = (((|x| : ℝ) : ℂ) ^ (z - 1)) * (Real.exp (-(Real.pi * |x| ^ 2)) : ℂ) := by
    intro x hx
    have habs0 : (0 : ℝ) < |x| := abs_pos.mpr hx
    have habsC : ((|x| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habs0.ne'
    rw [charExt_of_ne_zero (realCharFun u a) hx, realCharFun_val]
    simp only [realTestFun, Units.val_mk0]
    have hexp : Complex.exp (-(↑Real.pi * (x : ℂ) ^ 2))
        = (Real.exp (-(Real.pi * |x| ^ 2)) : ℂ) := by
      rw [Complex.ofReal_exp]
      push_cast [sq_abs]
      ring_nf
    have hnorm : ((‖x‖ : ℝ) : ℂ) = ((|x| : ℝ) : ℂ) := by
      norm_cast
    calc (↑x ^ a.val * Complex.exp (-(↑Real.pi * (x : ℂ) ^ 2)))
          * (((‖x‖ : ℝ) : ℂ) ^ u * ((x : ℂ) / ((‖x‖ : ℝ) : ℂ)) ^ (a.val : ℕ))
          * ((‖x‖ : ℂ) ^ (s - 1))
        = ((x : ℂ) ^ (a.val : ℕ) * ((x : ℂ) / ((‖x‖ : ℝ) : ℂ)) ^ (a.val : ℕ))
          * ((‖x‖ : ℝ) : ℂ) ^ u
          * ((‖x‖ : ℝ) : ℂ) ^ (s - 1)
          * Complex.exp (-(↑Real.pi * (x : ℂ) ^ 2)) := by
          ring
      _ = (((|x| : ℝ) : ℂ) ^ (a.val : ℕ)) * (((|x| : ℝ) : ℂ) ^ u)
          * (((|x| : ℝ) : ℂ) ^ (s - 1)) * (Real.exp (-(Real.pi * |x| ^ 2)) : ℂ) := by
          rw [pow_mul_sign_pow x hx, hnorm, hexp]
      _ = ((|x| : ℝ) : ℂ) ^ (z - 1) * (Real.exp (-(Real.pi * |x| ^ 2)) : ℂ) := by
          rw [← Complex.cpow_natCast ((|x| : ℝ) : ℂ) a.val]
          rw [← Complex.cpow_add _ _ habsC, ← Complex.cpow_add _ _ habsC]
          congr 2
          rw [hav, hzdef]
          ring
  have h0ae : ∀ᵐ (x : ℝ) ∂volume, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hcongr : realZeta volume (realTestFun a) (realCharFun u a) s
      = ∫ x : ℝ, (fun t : ℝ => ((t : ℂ) ^ (z - 1)) * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) |x| := by
    simp only [realZeta]
    refine integral_congr_ae (h0ae.mono fun x hx => ?_)
    exact hpt x hx
  rw [hcongr, integral_comp_abs_cx
    (f := fun t : ℝ => ((t : ℂ) ^ (z - 1)) * (Real.exp (-(Real.pi * t ^ 2)) : ℂ))]
  have hmel : (∫ x in Ioi (0:ℝ),
        (fun t : ℝ => ((t : ℂ) ^ (z - 1)) * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) x)
      = mellin (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) z := by
    simp only [mellin, smul_eq_mul]
  rw [hmel, mellin_gaussian hs]
  rw [Complex.Gammaℝ_def, neg_div]
  ring

end LanglandsTunnell.ArchPlace

end RealZeta

section ComplexZeta

open Real Set MeasureTheory MeasureTheory.Measure
open _root_.LanglandsTunnell open _root_.P2MW.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.LanglandsTunnell open _root_.LanglandsTunnell.TateLocal open _root_.LanglandsTunnell.ArchPlace open _root_.P2MW.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.LanglandsTunnell.ArchPlace
open scoped ENNReal

namespace LanglandsTunnell
export _root_.LanglandsTunnell (signShift)
namespace ArchPlace
export _root_.LanglandsTunnell.ArchPlace (anglePhase complexCharFun complexCharFun_apply complexTestFun complexZeta realSign realCharFun realTestFun realZeta)
open _root_.LanglandsTunnell.ArchPlace open _root_.LanglandsTunnell

end LanglandsTunnell.ArchPlace

end ComplexZeta

section FourierFormation

open _root_.MeasureTheory open _root_.LanglandsTunnell open _root_.P2MW.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.LanglandsTunnell open _root_.LanglandsTunnell.TateLocal open _root_.LanglandsTunnell.ArchPlace open _root_.P2MW.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.LanglandsTunnell.ArchPlace
open scoped ENNReal

namespace LanglandsTunnell
export _root_.LanglandsTunnell (signShift)
namespace ArchPlace
export _root_.LanglandsTunnell.ArchPlace (anglePhase complexCharFun complexCharFun_apply complexTestFun complexZeta realSign realCharFun realTestFun realZeta)
open _root_.LanglandsTunnell.ArchPlace open _root_.LanglandsTunnell

end LanglandsTunnell.ArchPlace

end FourierFormation

open _root_.MeasureTheory open _root_.LanglandsTunnell open _root_.P2MW.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.LanglandsTunnell open _root_.LanglandsTunnell.TateLocal open _root_.LanglandsTunnell.ArchPlace open _root_.P2MW.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.LanglandsTunnell.ArchPlace

theorem solution (u : ℂ) (a : ZMod 2) (s : ℂ)
    (hs : 0 < (s + (u + signShift a)).re) :
    realZeta volume (realTestFun a) (realCharFun u a) s = Complex.Gammaℝ (s + (u + signShift a)) := by
  exact LanglandsTunnell.ArchPlace.realZeta_realTestFun_realCharFun_eq_GammaReal u a s hs
