import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.FltAnthropic.Theorems.Thm_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel

set_option autoImplicit false

open MeasureTheory Set Filter

namespace LanglandsTunnell
namespace ArchBessel
export _root_.LanglandsTunnell.ArchBessel (besselKernel integrableOn_exp_neg_mul_add_inv_mul_cpow)
namespace DerivAux
open _root_.LanglandsTunnell.ArchBessel open _root_.LanglandsTunnell

noncomputable def g (x t : ℝ) : ℝ := Real.exp (-(x * (t + t⁻¹) / 2))

noncomputable def E (x t : ℝ) : ℂ := ((g x t : ℝ) : ℂ)

/--
@isnad1 id=lt.0h2v.s4.5f09c4f9a5cd from=translated src=- shape=a120b2a8 vocab=81a8323a
-/
theorem g_pos (x t : ℝ) : 0 < g x t := Real.exp_pos _

/--
@isnad1 id=eq.0h2v.s6.2b17ff2447be from=translated src=- shape=13379e1e vocab=675c59a3
-/
theorem besselKernel_eq (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ), E x t * ((t : ℂ) ^ (ν - 1)) := rfl

/--
@isnad1 id=integrab.1h2v.s6.c8591a0c38ab from=translated src=- shape=1f66612e vocab=f05a88f4
-/
theorem integrableOn_E_mul_cpow (μ : ℂ) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => E x t * ((t : ℂ) ^ (μ - 1))) (Ioi 0) :=
  integrableOn_exp_neg_mul_add_inv_mul_cpow μ x hx

/--
@isnad1 id=eq.1h3v.s6.ad632360b2f4 from=translated src=- shape=605301c9 vocab=65492fd9
-/
theorem norm_E_mul_cpow (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖E x t * (t : ℂ) ^ ν‖ = g x t * t ^ ν.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, E, Complex.norm_real,
    Real.norm_of_nonneg (g_pos x t).le]

/--
@isnad1 id=le.2h3v.s5.1915f1f905e6 from=translated src=- shape=668059f4 vocab=09be6b53
-/
theorem g_mono (x x' t : ℝ) (hxx' : x ≤ x') (ht : 0 < t) : g x' t ≤ g x t := by
  unfold g
  apply Real.exp_le_exp.mpr
  have : 0 ≤ t + t⁻¹ := by positivity
  nlinarith

/--
@isnad1 id=hasderiv.0h2v.s6.dc9cc04de603 from=translated src=- shape=2094d973 vocab=7c9b86b7
-/
theorem hasDerivAt_g (x t : ℝ) :
    HasDerivAt (fun y => g y t) (g x t * (-((t + t⁻¹) / 2))) x := by
  unfold g
  have h1 : HasDerivAt (fun y : ℝ => -(y * (t + t⁻¹) / 2)) (-(1 * (t + t⁻¹) / 2)) x :=
    (((hasDerivAt_id x).mul_const (t + t⁻¹)).div_const 2).neg
  have h2 := h1.exp
  convert h2 using 1 <;> ring

noncomputable def F' (ν : ℂ) (x t : ℝ) : ℂ :=
  -((E x t * (t : ℂ) ^ (ν - 1 - 1) + E x t * (t : ℂ) ^ (ν + 1 - 1)) / 2)

/--
@isnad1 id=hasderiv.1h3v.s6.6ae476de60eb from=translated src=- shape=268d11de vocab=304ce4a3
-/
theorem hasDerivAt_F (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => E y t * (t : ℂ) ^ (ν - 1)) (F' ν x t) x := by
  have hE : HasDerivAt (fun y : ℝ => E y t) ((g x t * (-((t + t⁻¹) / 2)) : ℝ) : ℂ) x :=
    (hasDerivAt_g x t).ofReal_comp
  have h := hE.mul_const ((t : ℂ) ^ (ν - 1))
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
@isnad1 id=hasderiv.1h2v.s7.f43ed0e55637 from=translated src=- shape=062aa695 vocab=427f5f1f
-/
theorem main (ν : ℂ) (x₀ : ℝ) (hx₀ : 0 < x₀) :
    HasDerivAt (fun x : ℝ => besselKernel ν x)
      (-(besselKernel (ν - 1) x₀ + besselKernel (ν + 1) x₀) / 2) x₀ := by
  have hx2 : 0 < x₀ / 2 := half_pos hx₀
  have hs : Ioi (x₀ / 2) ∈ nhds x₀ := Ioi_mem_nhds (by linarith)
  let bound : ℝ → ℝ := fun t =>
    (‖E (x₀ / 2) t * (t : ℂ) ^ (ν - 1 - 1)‖ + ‖E (x₀ / 2) t * (t : ℂ) ^ (ν + 1 - 1)‖) / 2
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (fun t : ℝ => E x t * (t : ℂ) ^ (ν - 1)) (volume.restrict (Ioi 0)) := by
    filter_upwards [hs] with x hx
    exact (integrableOn_E_mul_cpow ν x (lt_trans hx2 hx)).aestronglyMeasurable
  have hF_int : Integrable (fun t : ℝ => E x₀ t * (t : ℂ) ^ (ν - 1)) (volume.restrict (Ioi 0)) :=
    integrableOn_E_mul_cpow ν x₀ hx₀
  have hA : ∀ x : ℝ, 0 < x →
      Integrable (fun t : ℝ => E x t * (t : ℂ) ^ (ν - 1 - 1)) (volume.restrict (Ioi 0)) :=
    fun x hx => integrableOn_E_mul_cpow (ν - 1) x hx
  have hB : ∀ x : ℝ, 0 < x →
      Integrable (fun t : ℝ => E x t * (t : ℂ) ^ (ν + 1 - 1)) (volume.restrict (Ioi 0)) :=
    fun x hx => integrableOn_E_mul_cpow (ν + 1) x hx
  have hF'_int : Integrable (F' ν x₀) (volume.restrict (Ioi 0)) :=
    (((hA x₀ hx₀).add (hB x₀ hx₀)).div_const 2).neg
  have hF'_meas : AEStronglyMeasurable (F' ν x₀) (volume.restrict (Ioi 0)) :=
    hF'_int.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ Ioi (x₀ / 2), ‖F' ν x t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro x hx
    have ht' : 0 < t := ht
    have hxle : x₀ / 2 ≤ x := le_of_lt hx
    simp only [F', bound, norm_neg, norm_div, Complex.norm_ofNat]
    gcongr
    calc ‖E x t * (t : ℂ) ^ (ν - 1 - 1) + E x t * (t : ℂ) ^ (ν + 1 - 1)‖
        ≤ ‖E x t * (t : ℂ) ^ (ν - 1 - 1)‖ + ‖E x t * (t : ℂ) ^ (ν + 1 - 1)‖ := norm_add_le _ _
      _ ≤ ‖E (x₀ / 2) t * (t : ℂ) ^ (ν - 1 - 1)‖ + ‖E (x₀ / 2) t * (t : ℂ) ^ (ν + 1 - 1)‖ := by
          rw [norm_E_mul_cpow _ _ _ ht', norm_E_mul_cpow _ _ _ ht', norm_E_mul_cpow _ _ _ ht',
            norm_E_mul_cpow _ _ _ ht']
          gcongr
          · exact g_mono _ _ _ hxle ht'
          · exact g_mono _ _ _ hxle ht'
  have bound_integrable : Integrable bound (volume.restrict (Ioi 0)) :=
    ((hA _ hx2).norm.add (hB _ hx2).norm).div_const 2
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ Ioi (x₀ / 2),
      HasDerivAt (fun y : ℝ => E y t * (t : ℂ) ^ (ν - 1)) (F' ν x t) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro x _
    exact hasDerivAt_F ν x t ht
  have H := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff).2
  have hval : (∫ t, F' ν x₀ t ∂(volume.restrict (Ioi (0 : ℝ)))) =
      -(besselKernel (ν - 1) x₀ + besselKernel (ν + 1) x₀) / 2 := by
    show (∫ t in Ioi (0 : ℝ), F' ν x₀ t) = _
    unfold F'
    rw [integral_neg, integral_div, integral_add (hA x₀ hx₀) (hB x₀ hx₀), besselKernel_eq,
      besselKernel_eq, neg_div]
  rw [hval] at H
  exact H

end LanglandsTunnell.ArchBessel.DerivAux

open _root_.LanglandsTunnell.ArchBessel open _root_.P2MW.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel.LanglandsTunnell.ArchBessel

/--
@isnad1 id=hasderiv.1h2v.s7.f43ed0e55637 from=translated src=- shape=062aa695 vocab=427f5f1f
-/
theorem solution (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => besselKernel ν x)
      (-(besselKernel (ν - 1) x + besselKernel (ν + 1) x) / 2) x :=
  LanglandsTunnell.ArchBessel.DerivAux.main ν x hx
