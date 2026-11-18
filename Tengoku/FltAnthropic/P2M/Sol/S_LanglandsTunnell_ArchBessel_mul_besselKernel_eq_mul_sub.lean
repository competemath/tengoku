import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.FltAnthropic.Theorems.Thm_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub

set_option autoImplicit false

open MeasureTheory Set Filter

namespace LanglandsTunnell
namespace ArchBessel
export _root_.LanglandsTunnell.ArchBessel (besselKernel integrableOn_exp_neg_mul_add_inv_mul_cpow)
namespace IndexRecAux
open _root_.LanglandsTunnell.ArchBessel open _root_.LanglandsTunnell

noncomputable def g (x t : ℝ) : ℝ := Real.exp (-(x * (t + t⁻¹) / 2))

noncomputable def E (x t : ℝ) : ℂ := ((g x t : ℝ) : ℂ)

/--
@isnad1 id=eq.0h2v.s6.9af8dd344e19 from=translated src=- shape=13379e1e vocab=5dc7f3c9
-/
theorem besselKernel_eq (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ), E x t * ((t : ℂ) ^ (ν - 1)) := rfl

/--
@isnad1 id=integrab.1h2v.s6.e19f2d4d7afb from=translated src=- shape=1f66612e vocab=c00a2b64
-/
theorem integrableOn_E_mul_cpow (μ : ℂ) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => E x t * ((t : ℂ) ^ (μ - 1))) (Ioi 0) :=
  integrableOn_exp_neg_mul_add_inv_mul_cpow μ x hx

/--
@isnad1 id=hasderiv.1h2v.s6.950016e69d03 from=translated src=- shape=94d1c741 vocab=c7ebda47
-/
theorem hasDerivAt_g (x t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s => g x s) (g x t * (-(x * (1 - (t ^ 2)⁻¹) / 2))) t := by
  unfold g
  have h1 : HasDerivAt (fun s : ℝ => s + s⁻¹) (1 + (-(t ^ 2)⁻¹)) t :=
    (hasDerivAt_id t).add (hasDerivAt_inv ht)
  have h2 : HasDerivAt (fun s : ℝ => -(x * (s + s⁻¹) / 2)) (-(x * (1 + (-(t ^ 2)⁻¹)) / 2)) t :=
    ((h1.const_mul x).div_const 2).neg
  have h3 := h2.exp
  convert h3 using 1 <;> ring

/--
@isnad1 id=hasderiv.1h2v.s6.c0e1f3ae26cb from=translated src=- shape=5a93283e vocab=ed214651
-/
theorem hasDerivAt_ofReal_cpow (ν : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ ν) (ν * (t : ℂ) ^ (ν - 1)) t := by
  have h0 : (id (t : ℂ)) ∈ Complex.slitPlane := by
    simpa [Complex.ofReal_mem_slitPlane] using ht
  have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := ν) h0).comp_ofReal
  simpa using h

noncomputable def F' (ν : ℂ) (x t : ℝ) : ℂ :=
  ν * (E x t * (t : ℂ) ^ (ν - 1)) - (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1))
    + (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν - 1 - 1))

/--
@isnad1 id=hasderiv.1h3v.s6.fbb708e49f1e from=translated src=- shape=9dbe50bb vocab=47e3390c
-/
theorem hasDerivAt_E_mul_cpow (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => E x s * (s : ℂ) ^ ν) (F' ν x t) t := by
  have hE : HasDerivAt (fun s : ℝ => E x s) ((g x t * (-(x * (1 - (t ^ 2)⁻¹) / 2)) : ℝ) : ℂ) t :=
    (hasDerivAt_g x t ht.ne').ofReal_comp
  have h := hE.mul (hasDerivAt_ofReal_cpow ν t ht)
  refine h.congr_deriv ?_
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : (t : ℂ) ^ (ν + 1 - 1) = (t : ℂ) ^ ν := by rw [add_sub_cancel_right]
  have e2 : (t : ℂ) ^ (ν - 1 - 1) = (t : ℂ) ^ ν / (t : ℂ) ^ (2 : ℕ) := by
    rw [show ν - 1 - 1 = ν - 2 by ring, Complex.cpow_sub _ _ ht0, Complex.cpow_two]
  have e3 : (t : ℂ) ^ (ν - 1) = (t : ℂ) ^ ν / (t : ℂ) := by
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one]
  simp only [F', E, e1, e2, e3]
  push_cast
  field_simp
  ring

/--
@isnad1 id=lt.0h2v.s4.4e7566a98100 from=translated src=- shape=a120b2a8 vocab=15e413ac
-/
theorem g_pos (x t : ℝ) : 0 < g x t := Real.exp_pos _

/--
@isnad1 id=eq.1h3v.s6.e7ffd82dc831 from=translated src=- shape=605301c9 vocab=2640e2f1
-/
theorem norm_E_mul_cpow (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖E x t * (t : ℂ) ^ ν‖ = g x t * t ^ ν.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, E, Complex.norm_real,
    Real.norm_of_nonneg (g_pos x t).le]

/--
@isnad1 id=le.2h2v.s5.00f229f14e80 from=translated src=- shape=892e9e4d vocab=2bc888c9
-/
theorem g_le_exp_neg_mul (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    g x t ≤ Real.exp (-(x / 2) * t) := by
  unfold g
  apply Real.exp_le_exp.mpr
  have : 0 ≤ x * t⁻¹ := by positivity
  nlinarith

/--
@isnad1 id=le.2h2v.s6.37cdd4c63082 from=translated src=- shape=39066f97 vocab=595a57a0
-/
theorem g_le_exp_neg_mul_inv (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    g x t ≤ Real.exp (-(x / 2) * t⁻¹) := by
  unfold g
  apply Real.exp_le_exp.mpr
  have : 0 ≤ x * t := by positivity
  nlinarith

/--
@isnad1 id=tendsto.1h2v.s6.273834e915db from=translated src=- shape=8a1efa39 vocab=d6dccb91
-/
theorem tendsto_atTop (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => E x t * (t : ℂ) ^ ν) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ν.re (x / 2) (by positivity))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_E_mul_cpow ν x t ht, mul_comm]
  exact mul_le_mul_of_nonneg_left (g_le_exp_neg_mul x t hx ht) (Real.rpow_nonneg ht.le _)

/--
@isnad1 id=tendsto.1h2v.s6.27f066f90209 from=translated src=- shape=7e866cf4 vocab=2c1c3b84
-/
theorem tendsto_nhdsGT_zero (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => E x t * (t : ℂ) ^ ν) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-ν.re) (x / 2) (by positivity)).comp
    tendsto_inv_nhdsGT_zero
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  rw [norm_E_mul_cpow ν x t ht', Function.comp_apply, mul_comm]
  have hr : t ^ ν.re = (t⁻¹) ^ (-ν.re) := by
    rw [Real.rpow_neg (inv_nonneg.mpr ht'.le), Real.inv_rpow ht'.le, inv_inv]
  rw [hr]
  exact mul_le_mul_of_nonneg_left (g_le_exp_neg_mul_inv x t hx ht')
    (Real.rpow_nonneg (inv_nonneg.mpr ht'.le) _)

/--
@isnad1 id=eq.1h2v.s7.ea0fc8f2ad7f from=translated src=- shape=d66b6268 vocab=49870cbf
-/
theorem integral_F' (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), F' ν x t =
      ν * besselKernel ν x - (x : ℂ) / 2 * besselKernel (ν + 1) x
        + (x : ℂ) / 2 * besselKernel (ν - 1) x := by
  have h1 : Integrable (fun t : ℝ => ν * (E x t * (t : ℂ) ^ (ν - 1))) (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow ν x hx).const_mul ν
  have h2 : Integrable (fun t : ℝ => (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow (ν + 1) x hx).const_mul _
  have h3 : Integrable (fun t : ℝ => (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν - 1 - 1)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow (ν - 1) x hx).const_mul _
  have h12 : Integrable (fun t : ℝ => ν * (E x t * (t : ℂ) ^ (ν - 1))
      - (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1))) (volume.restrict (Ioi 0)) := h1.sub h2
  unfold F'
  rw [integral_add h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul,
    integral_const_mul, besselKernel_eq, besselKernel_eq, besselKernel_eq]

/--
@isnad1 id=eq.1h2v.s6.17ffb2546b81 from=translated src=- shape=fc3248d0 vocab=94517819
-/
theorem main (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ν * besselKernel ν x = (x : ℂ) / 2 * (besselKernel (ν + 1) x - besselKernel (ν - 1) x) := by
  classical
  let F : ℝ → ℂ := fun t => if 0 < t then E x t * (t : ℂ) ^ ν else 0
  have hFeq : EqOn F (fun t => E x t * (t : ℂ) ^ ν) (Ioi 0) := fun t ht => ite_eq_left ht
  have hF0 : F 0 = 0 := ite_eq_right (lt_irrefl 0)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (F' ν x t) t := by
    intro t ht
    exact (hasDerivAt_E_mul_cpow ν x t ht).congr_of_eventuallyEq
      (eventuallyEq_of_mem (Ioi_mem_nhds ht) hFeq)
  have hint : IntegrableOn (F' ν x) (Ioi 0) := by
    have h1 := (integrableOn_E_mul_cpow ν x hx).const_mul ν
    have h2 := (integrableOn_E_mul_cpow (ν + 1) x hx).const_mul ((x : ℂ) / 2)
    have h3 := (integrableOn_E_mul_cpow (ν - 1) x hx).const_mul ((x : ℂ) / 2)
    exact (h1.sub h2).add h3
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hF0]
    exact (tendsto_nhdsGT_zero ν x hx).congr' (eventuallyEq_of_mem self_mem_nhdsWithin hFeq).symm
  have hlim : Tendsto F atTop (nhds 0) :=
    (tendsto_atTop ν x hx).congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) hFeq).symm
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [hF0, sub_zero, integral_F' ν x hx] at hFTC
  linear_combination hFTC

end LanglandsTunnell.ArchBessel.IndexRecAux

open _root_.LanglandsTunnell.ArchBessel open _root_.P2MW.S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub.LanglandsTunnell.ArchBessel

/--
@isnad1 id=eq.1h2v.s6.17ffb2546b81 from=translated src=- shape=fc3248d0 vocab=94517819
-/
theorem solution (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ν * besselKernel ν x = (x : ℂ) / 2 * (besselKernel (ν + 1) x - besselKernel (ν - 1) x) :=
  LanglandsTunnell.ArchBessel.IndexRecAux.main ν x hx
