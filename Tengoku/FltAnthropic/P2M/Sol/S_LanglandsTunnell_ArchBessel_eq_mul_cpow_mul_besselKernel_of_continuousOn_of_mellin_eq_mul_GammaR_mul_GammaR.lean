import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.FltAnthropic.Theorems.Thm_LanglandsTunnell_ArchBessel_mellin_besselKernel_eq_mul_Gamma_mul_Gamma
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ArchBessel_eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ArchBessel_eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR

set_option autoImplicit false

open _root_.MeasureTheory open _root_.Set open _root_.Real open _root_.Complex open _root_.LanglandsTunnell.ArchBessel

noncomputable section

namespace LanglandsTunnell
export _root_.LanglandsTunnell (ArchBessel.mellin_besselKernel_eq_mul_Gamma_mul_Gamma)
namespace ArchBessel
export _root_.LanglandsTunnell.ArchBessel (besselKernel mellin_besselKernel_eq_mul_Gamma_mul_Gamma)
namespace MellinK
open _root_.LanglandsTunnell.ArchBessel open _root_.LanglandsTunnell

theorem integrable_of_integral_ne_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} (h : ∫ x, f x ∂μ ≠ 0) : Integrable f μ := by
  by_contra hf
  exact h (integral_undef hf)

theorem integrableOn_rpow_mul_exp_neg_mul {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  exact mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos ha).ne'

theorem integral_rpow_mul_exp_neg_mul_sq {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), t ^ (2 * a - 1) * Real.exp (-(y * t ^ 2)) = (1 / 2) * ((1 / y) ^ a * Real.Gamma a) := by
  have hsub := integral_comp_rpow_Ioi
    (fun u : ℝ => u ^ (a - 1) * Real.exp (-(y * u))) (p := 2) two_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hy] at hsub
  have hcongr : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        ((x ^ (2 : ℝ)) ^ (a - 1) * Real.exp (-(y * x ^ (2 : ℝ)))) =
      ∫ x in Ioi (0 : ℝ), 2 * (x ^ (2 * a - 1) * Real.exp (-(y * x ^ 2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx : 0 < x := hx
    have e1 : (x ^ (2 : ℝ)) ^ (a - 1) = x ^ (2 * (a - 1)) := by rw [← Real.rpow_mul hx.le]
    have e2 : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_two x
    have e3 : |(2 : ℝ)| * x ^ ((2 : ℝ) - 1) = 2 * x := by norm_num
    rw [e3, e1, e2, smul_eq_mul]
    have e4 : x * x ^ (2 * (a - 1)) = x ^ (2 * a - 1) := by
      rw [show x * x ^ (2 * (a - 1)) = x ^ (1 : ℝ) * x ^ (2 * (a - 1)) by rw [Real.rpow_one],
        ← Real.rpow_add hx]
      congr 1; ring
    calc 2 * x * (x ^ (2 * (a - 1)) * Real.exp (-(y * x ^ 2)))
        = 2 * ((x * x ^ (2 * (a - 1))) * Real.exp (-(y * x ^ 2))) := by ring
      _ = _ := by rw [e4]
  rw [hcongr, integral_const_mul] at hsub
  linarith

theorem integrableOn_rpow_mul_exp_neg_mul_sq {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t ^ (2 * a - 1) * Real.exp (-(y * t ^ 2))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [integral_rpow_mul_exp_neg_mul_sq ha hy]
  exact mul_ne_zero (by norm_num) (mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos ha).ne')

theorem integrableOn_rpow_mul_exp_neg_mul_add_inv {c : ℝ} (hc : 0 < c) (n : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (n - 1) * Real.exp (-(c * (t + t⁻¹)))) (Ioi 0) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-n)
  have hnk : 0 < n + k := by linarith
  have hI := (integrableOn_rpow_mul_exp_neg_mul hnk hc).const_mul ((k.factorial : ℝ) / c ^ k)
  have hmeas : Measurable (fun t : ℝ => t ^ (n - 1) * Real.exp (-(c * (t + t⁻¹)))) :=
    (measurable_id.pow_const _).mul (Real.measurable_exp.comp ((measurable_const.mul
      (measurable_id.add measurable_inv)).neg))
  refine hI.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
  have ht : 0 < t := ht
  have hct : 0 < c / t := div_pos hc ht

  have hexp : Real.exp (-(c * t⁻¹)) ≤ (k.factorial : ℝ) / c ^ k * t ^ (k : ℝ) := by
    have h1 := Real.pow_div_factorial_le_exp (c / t) hct.le k
    have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hpos : 0 < (c / t) ^ k / k.factorial := by positivity
    rw [show -(c * t⁻¹) = -(c / t) by ring, Real.exp_neg]
    calc (Real.exp (c / t))⁻¹ ≤ ((c / t) ^ k / k.factorial)⁻¹ := inv_anti₀ hpos h1
      _ = (k.factorial : ℝ) / c ^ k * t ^ (k : ℝ) := by
          rw [Real.rpow_natCast, div_pow]; field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
  have esplit : Real.exp (-(c * (t + t⁻¹))) = Real.exp (-(c * t)) * Real.exp (-(c * t⁻¹)) := by
    rw [← Real.exp_add]; ring_nf
  rw [esplit]
  calc t ^ (n - 1) * (Real.exp (-(c * t)) * Real.exp (-(c * t⁻¹)))
      ≤ t ^ (n - 1) * (Real.exp (-(c * t)) * ((k.factorial : ℝ) / c ^ k * t ^ (k : ℝ))) := by
        gcongr
    _ = (k.factorial : ℝ) / c ^ k * (t ^ (n + k - 1) * Real.exp (-(c * t))) := by
        rw [show n + (k : ℝ) - 1 = (n - 1) + k by ring, Real.rpow_add ht]; ring

theorem norm_besselIntegrand (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖(Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))‖ =
      t ^ (ν.re - 1) * Real.exp (-(x / 2 * (t + t⁻¹))) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re, mul_comm]
  congr 1; ring_nf

theorem continuousAt_besselKernel (ν : ℂ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (fun x : ℝ => besselKernel ν x) x₀ := by
  unfold besselKernel
  have hmeasF : ∀ x : ℝ, Measurable (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) :=
    fun x => (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_const.mul (measurable_id.add measurable_inv)).div_const 2).neg))).mul
      ((Complex.measurable_ofReal.comp measurable_id).pow_const _)
  refine continuousAt_of_dominated (bound := fun t : ℝ => t ^ (ν.re - 1) * Real.exp (-(x₀ / 4 * (t + t⁻¹))))
    (Filter.Eventually.of_forall fun x => (hmeasF x).aestronglyMeasurable) ?_ ?_ ?_
  ·
    filter_upwards [Ioi_mem_nhds (show x₀ / 2 < x₀ by linarith)] with x hx
    have hx : x₀ / 2 < x := hx
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have ht : 0 < t := ht
    rw [norm_besselIntegrand ν x t ht]
    have hsum : 0 < t + t⁻¹ := by positivity
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    nlinarith
  · exact integrableOn_rpow_mul_exp_neg_mul_add_inv (by linarith) ν.re
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun t _ => ?_)
    exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_id.mul continuous_const).div_const 2).neg)).mul continuous_const).continuousAt

end LanglandsTunnell.ArchBessel.MellinK

end

open LanglandsTunnell.ArchBessel.MellinK in
theorem solution
    (f : ℝ → ℂ) (A p q : ℂ) (σ₀ : ℝ)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hM : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent f s ∧ mellin f s = A * Complex.Gammaℝ (s + p) * Complex.Gammaℝ (s + q)) :
    ∀ t : ℝ, 0 < t →
      f t = 2 * A * ((t : ℂ) ^ ((p + q) / 2)) * besselKernel ((p - q) / 2) (2 * Real.pi * t) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero
  set m : ℂ := (p + q) / 2 with hm
  set ν : ℂ := (p - q) / 2 with hν
  have hK := fun (s : ℂ) (hs : |ν.re| < s.re) =>
    LanglandsTunnell.ArchBessel.mellin_besselKernel_eq_mul_Gamma_mul_Gamma ν s hs

  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun t : ℝ => 2 * A * ((t : ℂ) ^ m) * besselKernel ν (2 * Real.pi * t) :=
    ⟨_, rfl⟩
  have hgE : g = fun t : ℝ => (2 * A) • ((t : ℂ) ^ m • (fun x : ℝ => besselKernel ν x) (2 * Real.pi * t)) := by
    funext t; simp only [hg, smul_eq_mul]; ring
  have hGconv : ∀ s : ℂ, |ν.re| - m.re < s.re → MellinConvergent g s := by
    intro s hs
    rw [hgE]
    refine MellinConvergent.const_smul ?_ (2 * A)
    rw [MellinConvergent.cpow_smul, MellinConvergent.comp_mul_left h2π]
    exact (hK _ (by simp; linarith)).1
  have hGmel : ∀ s : ℂ, |ν.re| - m.re < s.re →
      mellin g s = A * Complex.Gammaℝ (s + p) * Complex.Gammaℝ (s + q) := by
    intro s hs
    rw [hgE, mellin_const_smul, mellin_cpow_smul, mellin_comp_mul_left _ _ h2π, (hK _ (by simp; linarith)).2,
      smul_eq_mul, smul_eq_mul, Complex.Gammaℝ_def, Complex.Gammaℝ_def]
    have hΓ1 : (s + m + ν) / 2 = (s + p) / 2 := by rw [hm, hν]; ring
    have hΓ2 : (s + m - ν) / 2 = (s + q) / 2 := by rw [hm, hν]; ring
    rw [hΓ1, hΓ2]
    have e2 : (2 : ℂ) * ((((2 * Real.pi : ℝ) : ℂ)) ^ (-(s + m)) * (2 : ℂ) ^ (s + m - 1)) =
        (Real.pi : ℂ) ^ (-(s + m)) := by
      have : (((2 * Real.pi : ℝ) : ℂ)) = ((2 : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.mul_cpow_ofReal_nonneg (by norm_num) hπ.le]
      push_cast
      have h2a : (2 : ℂ) * ((2 : ℂ) ^ (-(s + m)) * (2 : ℂ) ^ (s + m - 1)) = 1 := by
        rw [← Complex.cpow_add _ _ h20, show (2 : ℂ) * (2 : ℂ) ^ (-(s + m) + (s + m - 1)) =
          (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-(s + m) + (s + m - 1)) by rw [Complex.cpow_one],
          ← Complex.cpow_add _ _ h20]
        ring_nf
        exact Complex.cpow_zero _
      calc (2 : ℂ) * ((2 : ℂ) ^ (-(s + m)) * (Real.pi : ℂ) ^ (-(s + m)) * (2 : ℂ) ^ (s + m - 1))
          = ((2 : ℂ) * ((2 : ℂ) ^ (-(s + m)) * (2 : ℂ) ^ (s + m - 1))) * (Real.pi : ℂ) ^ (-(s + m)) := by ring
        _ = (Real.pi : ℂ) ^ (-(s + m)) := by rw [h2a, one_mul]
    have eπ : (Real.pi : ℂ) ^ (-(s + p) / 2) * (Real.pi : ℂ) ^ (-(s + q) / 2) = (Real.pi : ℂ) ^ (-(s + m)) := by
      rw [← Complex.cpow_add _ _ hπ0]; congr 1; rw [hm]; ring
    linear_combination (A * Complex.Gamma ((s + p) / 2) * Complex.Gamma ((s + q) / 2)) * e2 -
      (A * Complex.Gamma ((s + p) / 2) * Complex.Gamma ((s + q) / 2)) * eπ

  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℂ, h = fun t : ℝ => f t - g t := ⟨_, rfl⟩
  have hHconv : ∀ s : ℂ, σ₀ < s.re → |ν.re| - m.re < s.re → MellinConvergent h s ∧ mellin h s = 0 := by
    intro s hs1 hs2
    obtain ⟨hf1, hf2⟩ := hM s hs1
    have hg1 := hGconv s hs2
    have hg2 := hGmel s hs2
    have hint : MellinConvergent h s := by
      have := (MeasureTheory.Integrable.sub hf1 hg1)
      refine this.congr ?_
      filter_upwards with t
      simp only [hh, smul_sub, Pi.sub_apply]
    refine ⟨hint, ?_⟩
    have : mellin h s = mellin f s - mellin g s := by
      unfold mellin
      rw [← MeasureTheory.integral_sub hf1 hg1]
      congr 1
      funext t
      simp only [hh, smul_sub]
    rw [this, hf2, hg2, sub_self]

  obtain ⟨σ, hσ₀, hσν⟩ : ∃ σ : ℝ, σ₀ < σ ∧ |ν.re| - m.re < σ :=
    ⟨max σ₀ (|ν.re| - m.re) + 1, by have := le_max_left σ₀ (|ν.re| - m.re); linarith,
      by have := le_max_right σ₀ (|ν.re| - m.re); linarith⟩
  have hre : ∀ y : ℝ, ((σ : ℂ) + (y : ℂ) * I).re = σ := by intro y; simp
  have hline : ∀ y : ℝ, mellin h ((σ : ℂ) + (y : ℂ) * I) = 0 := fun y =>
    (hHconv _ (by rw [hre]; exact hσ₀) (by rw [hre]; exact hσν)).2
  have hconvσ : MellinConvergent h (σ : ℂ) :=
    (hHconv _ (by rw [Complex.ofReal_re]; exact hσ₀) (by rw [Complex.ofReal_re]; exact hσν)).1
  intro t ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hcontf : ContinuousAt f t := hcont.continuousAt (Ioi_mem_nhds ht)
  have hcontg : ContinuousAt g t := by
    rw [hg]
    have h1 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ m) t :=
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')
    have h2 : ContinuousAt (fun u : ℝ => besselKernel ν (2 * Real.pi * u)) t := by
      have hk : ContinuousAt (fun x : ℝ => besselKernel ν x) (2 * Real.pi * t) :=
        continuousAt_besselKernel ν (by positivity)
      exact hk.comp (f := fun u : ℝ => 2 * Real.pi * u) (continuous_const.mul continuous_id).continuousAt
    exact ((continuousAt_const.mul h1).mul h2)
  have hconth : ContinuousAt h t := by
    rw [hh]
    exact hcontf.sub hcontg
  have hvert : VerticalIntegrable (mellin h) σ := by
    unfold VerticalIntegrable
    have hz : (fun y : ℝ => mellin h (↑σ + ↑y * I)) = fun _ => (0 : ℂ) := funext hline
    rw [hz]
    exact MeasureTheory.integrable_zero _ _ _
  have hinv := mellinInv_mellin_eq σ h ht hconvσ hvert hconth
  have hzero : mellinInv σ (mellin h) t = 0 := by
    unfold mellinInv
    have hz : (fun y : ℝ => (t : ℂ) ^ (-(↑σ + ↑y * I)) • mellin h (↑σ + ↑y * I)) = fun _ => 0 := by
      funext y
      rw [hline y, smul_zero]
    rw [hz, MeasureTheory.integral_zero, smul_zero]
  have hft : f t = g t := by
    have : h t = 0 := by rw [← hinv, hzero]
    rw [hh] at this
    exact sub_eq_zero.mp this
  rw [hft, hg]

