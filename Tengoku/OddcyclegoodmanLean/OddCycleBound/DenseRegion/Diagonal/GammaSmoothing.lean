import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.KernelIntegrable
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.GammaMoment
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.ShiftedGammaPositive
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.Positivity
import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.DenseRegion

lemma powExpMul_integrableOn (m : ℕ) (w : ℝ) (hw : 0 < w) :
    IntegrableOn (fun T => T ^ (m - 1) * Real.exp (-(w * T))) (Set.Ioi (0 : ℝ)) := by
  have hg : IntegrableOn (fun x => x ^ (m - 1) * Real.exp (-x)) (Set.Ioi (0 : ℝ)) := by
    have hc := Real.GammaIntegral_convergent (s := ((m - 1 : ℕ) : ℝ) + 1) (by positivity)
    refine hc.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show Real.exp (-x) * x ^ (((m - 1 : ℕ) : ℝ) + 1 - 1) = x ^ (m - 1) * Real.exp (-x)
    rw [show ((m - 1 : ℕ) : ℝ) + 1 - 1 = ((m - 1 : ℕ) : ℝ) from by ring, Real.rpow_natCast]
    ring
  have hscaled : IntegrableOn (fun T => (w * T) ^ (m - 1) * Real.exp (-(w * T))) (Set.Ioi (0 : ℝ)) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x => x ^ (m - 1) * Real.exp (-x)) 0 hw).mpr (by simpa using hg)
    simpa using h
  refine IntegrableOn.congr_fun (hscaled.const_mul ((w ^ (m - 1))⁻¹))
    (fun T _ => ?_) measurableSet_Ioi
  have hwne : (w ^ (m - 1) : ℝ) ≠ 0 := by positivity
  rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hwne, one_mul]

lemma smoothing_inner (n m r : ℕ) (hr : 1 ≤ r) (q T : ℝ) (hT : 0 < T) :
    ∫ s in Set.Ioi (0 : ℝ), s ^ (r - 1) * rho n m (q + s) * Real.exp (-(T * s))
      = (T ^ r)⁻¹ * gExp r (fun y => rho n m (q + y / T)) := by
  have hcomp := integral_comp_mul_left_Ioi
    (fun y => y ^ (r - 1) * Real.exp (-y) * rho n m (q + y / T)) 0 hT
  simp only [mul_zero, smul_eq_mul] at hcomp
  have hlhs : (∫ x in Set.Ioi (0 : ℝ),
        (T * x) ^ (r - 1) * Real.exp (-(T * x)) * rho n m (q + T * x / T))
      = T ^ (r - 1) * ∫ s in Set.Ioi (0 : ℝ), s ^ (r - 1) * rho n m (q + s) * Real.exp (-(T * s)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [show T * x / T = x from by rw [mul_comm T x, mul_div_assoc, div_self (ne_of_gt hT), mul_one],
      mul_pow]
    ring
  rw [hlhs] at hcomp
  have hgExp : gExp r (fun y => rho n m (q + y / T))
      = ∫ x in Set.Ioi (0 : ℝ), x ^ (r - 1) * Real.exp (-x) * rho n m (q + x / T) := rfl
  rw [← hgExp] at hcomp
  have hne : (T ^ (r - 1) : ℝ) ≠ 0 := by positivity
  have hTr : (T ^ r : ℝ) = T ^ (r - 1) * T := by rw [← pow_succ]; congr 1; omega
  rw [hTr, mul_inv, mul_assoc, ← hcomp, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

lemma smoothing_jointIntegrable {m r : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ m - 2 * r) (q ℓ : ℝ) (hl : 0 < ℓ) :
    Integrable (Function.uncurry (fun s T => s ^ (r - 1) * rho (m - 2 * r) m (q + s)
        * (T ^ (m - 1) * Real.exp (-((ℓ + s) * T)))))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  set F : ℝ → ℝ → ℝ := fun s T => s ^ (r - 1) * rho (m - 2 * r) m (q + s)
      * (T ^ (m - 1) * Real.exp (-((ℓ + s) * T))) with hF
  have hrne : r ≠ 0 := by omega
  have hm1 : 1 ≤ m := by omega
  have hrho_cont : Continuous (fun u => rho (m - 2 * r) m u) := by unfold rho; fun_prop
  have huF : Continuous (Function.uncurry F) := by
    have h2 : Continuous (fun p : ℝ × ℝ => rho (m - 2 * r) m (q + p.1)) :=
      hrho_cont.comp (continuous_const.add continuous_fst)
    exact ((continuous_fst.pow _).mul h2).mul ((continuous_snd.pow _).mul
      (Real.continuous_exp.comp (((continuous_const.add continuous_fst).mul continuous_snd).neg)))
  refine (integrable_prod_iff huF.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    rw [Set.mem_Ioi] at hs
    refine IntegrableOn.congr_fun ((powExpMul_integrableOn m (ℓ + s) (by linarith)).const_mul
      (s ^ (r - 1) * rho (m - 2 * r) m (q + s))) (fun T _ => ?_) measurableSet_Ioi
    simp only [hF, Function.uncurry_apply_pair]
  · have hconst := ((kernelIntegrand_integrableOn hrne hn q ℓ hl).norm).const_mul
      (Nat.factorial (m - 1) : ℝ)
    refine IntegrableOn.congr_fun hconst (fun s hs => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at hs
    simp only [Function.uncurry_apply_pair]
    have hℓs : (0 : ℝ) < ℓ + s := by linarith
    have hnormeq : ∀ T ∈ Set.Ioi (0 : ℝ), ‖F s T‖
        = ‖s ^ (r - 1) * rho (m - 2 * r) m (q + s)‖ * (T ^ (m - 1) * Real.exp (-((ℓ + s) * T))) := by
      intro T hT; rw [Set.mem_Ioi] at hT
      simp only [hF, mul_assoc, norm_mul,
        Real.norm_of_nonneg (mul_nonneg (pow_nonneg hT.le _) (Real.exp_pos _).le)]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hnormeq,
      MeasureTheory.integral_const_mul, intPowExpMul m hm1 (ℓ + s) hℓs]
    unfold kernelIntegrand
    rw [show s ^ (r - 1) / (ℓ + s) ^ m * rho (m - 2 * r) m (q + s)
        = s ^ (r - 1) * rho (m - 2 * r) m (q + s) / (ℓ + s) ^ m from by ring,
      norm_div, Real.norm_of_nonneg (pow_nonneg hℓs.le m)]
    ring

theorem kernelIntegral_nonneg {m r t : ℕ} (hr : 1 ≤ r) (ht : m - 2 * r = 2 * t + 1)
    (hmoment : ∀ j : ℕ, 1 ≤ j → ∀ z : ℝ, 0 ≤ z →
      3 * (j : ℝ) * gExp r (fun y => (z * y - 1) ^ (2 * j - 1))
        ≤ ((r : ℝ) + j) * gExp r (fun y => (z * y - 1) ^ (2 * j)))
    (q ℓ : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hl : 0 < ℓ) :
    0 ≤ ∫ s in Set.Ioi (0 : ℝ), s ^ (r - 1) / (ℓ + s) ^ m * rho (m - 2 * r) m (q + s) := by
  have hrne : r ≠ 0 := by omega
  have hn : 1 ≤ m - 2 * r := by omega
  have hm1 : 1 ≤ m := by omega
  have hm : m = 2 * t + 1 + 2 * r := by omega
  have hfac : (Nat.factorial (m - 1) : ℝ) ≠ 0 := by positivity
  set F : ℝ → ℝ → ℝ := fun s T => s ^ (r - 1) * rho (m - 2 * r) m (q + s)
      * (T ^ (m - 1) * Real.exp (-((ℓ + s) * T))) with hF

  have hstep2 : (∫ s in Set.Ioi (0 : ℝ), s ^ (r - 1) / (ℓ + s) ^ m * rho (m - 2 * r) m (q + s))
      = ((Nat.factorial (m - 1) : ℝ))⁻¹ * ∫ s in Set.Ioi (0 : ℝ), ∫ T in Set.Ioi (0 : ℝ), F s T := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    rw [Set.mem_Ioi] at hs
    have hℓs : (0 : ℝ) < ℓ + s := by linarith
    have hden : ((ℓ + s) ^ m : ℝ) ≠ 0 := by positivity
    rw [show (∫ T in Set.Ioi (0 : ℝ), F s T)
          = s ^ (r - 1) * rho (m - 2 * r) m (q + s) * ((Nat.factorial (m - 1) : ℝ) / (ℓ + s) ^ m) from by
        simp only [hF]; rw [MeasureTheory.integral_const_mul, intPowExpMul m hm1 (ℓ + s) hℓs]]
    field_simp

  rw [hstep2, MeasureTheory.integral_integral_swap (smoothing_jointIntegrable hr hn q ℓ hl)]

  have hinnerT : ∀ T ∈ Set.Ioi (0 : ℝ), (∫ s in Set.Ioi (0 : ℝ), F s T)
      = T ^ (m - 1) * Real.exp (-(ℓ * T)) * ((T ^ r)⁻¹ * gExp r (fun y => rho (m - 2 * r) m (q + y / T))) := by
    intro T hT; rw [Set.mem_Ioi] at hT
    rw [show (∫ s in Set.Ioi (0 : ℝ), F s T)
          = T ^ (m - 1) * Real.exp (-(ℓ * T))
            * ∫ s in Set.Ioi (0 : ℝ), s ^ (r - 1) * rho (m - 2 * r) m (q + s) * Real.exp (-(T * s)) from by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
        simp only [hF]
        rw [show -((ℓ + s) * T) = -(ℓ * T) + -(T * s) from by ring, Real.exp_add]; ring,
      smoothing_inner (m - 2 * r) m r hr q T hT]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hinnerT]

  refine mul_nonneg (by positivity) (MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun T hT => ?_))
  rw [Set.mem_Ioi] at hT
  refine mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (mul_nonneg (by positivity) ?_)
  have hfun : (fun y : ℝ => rho (m - 2 * r) m (q + y / T))
      = fun y => rho (2 * t + 1) (2 * t + 1 + 2 * r) (q + 1 / T * y) := by
    funext y
    rw [ht, hm, show y / T = 1 / T * y from by rw [div_eq_mul_inv, one_div, mul_comm]]
  rw [hfun]
  exact shifted_gamma_positive_of_moment_bound t r hr hmoment q (1 / T) hq0 hq (by positivity)

theorem diagKernel_nonneg_pos_ell
    (hmoment : ∀ r : ℕ, 1 ≤ r → ∀ j : ℕ, 1 ≤ j → ∀ z : ℝ, 0 ≤ z →
      3 * (j : ℝ) * gExp r (fun y => (z * y - 1) ^ (2 * j - 1))
        ≤ ((r : ℝ) + j) * gExp r (fun y => (z * y - 1) ^ (2 * j))) :
    DiagKernelPosEll := by
  intro m r t hr ht q ℓ hq0 hq hl
  have hn : 1 ≤ m - 2 * r := by omega
  rw [kernel_form (by omega) hn q ℓ hl]
  refine mul_nonneg (mul_nonneg (Cmr_pos (by omega) hn).le (by positivity)) ?_
  exact kernelIntegral_nonneg hr ht (hmoment r hr) q ℓ hq0 hq hl

end OddCycleBound.DenseRegion
