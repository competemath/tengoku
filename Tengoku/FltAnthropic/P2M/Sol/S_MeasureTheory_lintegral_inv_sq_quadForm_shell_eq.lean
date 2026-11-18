import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_lintegral_inv_sq_quadForm_shell_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_lintegral_inv_sq_quadForm_shell_eq

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace ShellIntegral

open Real Set

def F (v : ℝ) : ENNReal := (Set.Icc (1 : ℝ) (Real.exp 2)).indicator (fun v => (ENNReal.ofReal (v ^ 2))⁻¹) v

/--
@isnad1 id=measurab.0h0v.s2.f56a0055d5bf from=translated src=- shape=54c8eceb vocab=f6842460
-/
theorem measurable_F : Measurable F := by
  unfold F
  exact (Measurable.ennreal_ofReal (measurable_id.pow_const 2)).inv.indicator measurableSet_Icc

def f (v : ℝ) : ℝ := (Set.Icc (1 : ℝ) (Real.exp 2)).indicator (fun v => (v ^ 2)⁻¹) v

/--
@isnad1 id=measurab.0h0v.s2.f8d87ff130da from=translated src=- shape=e3d48bcb vocab=eda32255
-/
theorem measurable_f : Measurable f := by
  unfold f
  exact ((measurable_id.pow_const 2).inv).indicator measurableSet_Icc

/--
@isnad1 id=eq.0h1v.s3.1e7e00e5de7d from=translated src=- shape=69b989be vocab=5131106d
-/
theorem F_eq_ofReal_f (v : ℝ) : F v = ENNReal.ofReal (f v) := by
  unfold F f
  by_cases hv : v ∈ Set.Icc (1 : ℝ) (Real.exp 2)
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, ENNReal.ofReal_inv_of_pos]
    exact pow_pos (lt_of_lt_of_le one_pos hv.1) 2
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, ENNReal.ofReal_zero]

/--
@isnad1 id=le.0h1v.s3.59efbd2ad06b from=translated src=- shape=8a62b088 vocab=0358c00a
-/
theorem f_nonneg (v : ℝ) : 0 ≤ f v := by
  unfold f
  exact Set.indicator_nonneg (fun _ _ => inv_nonneg.2 (sq_nonneg _)) v

/--
@isnad1 id=eq.0h0v.s5.e9e4d6f04db5 from=translated src=- shape=8911115d vocab=3e41f8b2
-/
theorem exp_two_eq_sq : Real.exp 2 = Real.exp 1 ^ 2 := by
  rw [← Real.exp_nat_mul]; norm_num

abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/--
@isnad1 id=eq.0h0v.s9.844d6b48d8cf from=translated src=- shape=b7a82930 vocab=59037e90
-/
theorem volume_ball_E4 : (volume (Metric.ball (0 : E4) 1)).toReal = Real.pi ^ 2 / 2 := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  have hG : Real.Gamma ((4 : ℕ) / 2 + 1 : ℝ) = 2 := by
    rw [show ((4 : ℕ) / 2 + 1 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hG, show Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt Real.pi_pos.le]]
  rw [ENNReal.toReal_ofReal (by positivity)]

/--
@isnad1 id=eqon.0h0v.s6.fb3e0ae0d049 from=translated src=- shape=8ac8efb6 vocab=e25ba962
-/
theorem profile_eqOn : Set.EqOn (fun y : ℝ => y ^ (4 - 1) • f (y ^ 2))
    (fun y => (Set.Icc (1 : ℝ) (Real.exp 1)).indicator (fun y => y⁻¹) y) (Set.Ioi 0) := by
  intro y hy
  have hy0 : 0 < y := hy
  simp only [f, smul_eq_mul]
  by_cases hmem : y ∈ Set.Icc (1 : ℝ) (Real.exp 1)
  · have h2 : y ^ 2 ∈ Set.Icc (1 : ℝ) (Real.exp 2) := by
      rw [exp_two_eq_sq]
      exact ⟨by nlinarith [hmem.1], pow_le_pow_left₀ hy0.le hmem.2 2⟩
    rw [Set.indicator_of_mem h2, Set.indicator_of_mem hmem]
    field_simp
  · have h2 : y ^ 2 ∉ Set.Icc (1 : ℝ) (Real.exp 2) := by
      intro h2
      apply hmem
      rw [exp_two_eq_sq] at h2
      refine ⟨?_, ?_⟩
      · exact (pow_le_pow_iff_left₀ zero_le_one hy0.le two_ne_zero).1 (by simpa using h2.1)
      · exact (pow_le_pow_iff_left₀ hy0.le (Real.exp_pos 1).le two_ne_zero).1 h2.2
    rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem hmem, mul_zero]

/--
@isnad1 id=le.0h0v.s4.718e82006212 from=translated src=- shape=cf0a9d99 vocab=1ef57d49
-/
theorem one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ); linarith

/--
@isnad1 id=eq.0h0v.s6.4a0bec4b68fc from=translated src=- shape=053cd51b vocab=d751d9d9
-/
theorem integral_profile : ∫ y in Set.Ioi (0 : ℝ), y ^ (4 - 1) • f (y ^ 2) = 1 := by
  rw [setIntegral_congr_fun measurableSet_Ioi profile_eqOn, setIntegral_indicator measurableSet_Icc,
    show Set.Ioi (0 : ℝ) ∩ Set.Icc 1 (Real.exp 1) = Set.Icc 1 (Real.exp 1) from
      Set.inter_eq_right.2 fun y hy => lt_of_lt_of_le one_pos hy.1,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le one_le_exp_one,
    integral_inv_of_pos one_pos (Real.exp_pos 1), div_one, Real.log_exp]

/--
@isnad1 id=integrab.0h0v.s6.5907dab717a7 from=translated src=- shape=a380185f vocab=62e2ca48
-/
theorem integrableOn_profile : IntegrableOn (fun y : ℝ => y ^ (4 - 1) • f (y ^ 2)) (Set.Ioi 0) := by
  refine IntegrableOn.congr_fun ?_ profile_eqOn.symm measurableSet_Ioi
  refine Integrable.integrableOn ?_
  rw [integrable_indicator_iff measurableSet_Icc]
  exact (continuousOn_inv₀.mono fun y hy => (lt_of_lt_of_le one_pos hy.1).ne').integrableOn_Icc

/--
@isnad1 id=eq.0h0v.s8.3c3820f31cd6 from=translated src=- shape=0ca3cd8a vocab=e8363c2c
-/
theorem integral_radial : ∫ x : E4, f (‖x‖ ^ 2) = 2 * Real.pi ^ 2 := by
  have h := MeasureTheory.integral_fun_norm_addHaar (volume : Measure E4) (fun r => f (r ^ 2))
  rw [h, finrank_euclideanSpace, Fintype.card_fin, integral_profile, Measure.real, volume_ball_E4]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

/--
@isnad1 id=integrab.0h0v.s8.e7f24316ce1d from=translated src=- shape=760ce18e vocab=b4dc3ec3
-/
theorem integrable_radial : Integrable (fun x : E4 => f (‖x‖ ^ 2)) := by
  have h := (MeasureTheory.integrable_fun_norm_addHaar (volume : Measure E4) (f := fun r => f (r ^ 2))).2
  exact h (by rw [finrank_euclideanSpace, Fintype.card_fin]; exact integrableOn_profile)

/--
@isnad1 id=eq.0h0v.s8.03a9c0189939 from=translated src=- shape=a0404acf vocab=33a6cee4
-/
theorem lintegral_radial : ∫⁻ x : E4, F (‖x‖ ^ 2) = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  have : (fun x : E4 => F (‖x‖ ^ 2)) = fun x => ENNReal.ofReal (f (‖x‖ ^ 2)) := by
    funext x; exact F_eq_ofReal_f _
  rw [this, ← ofReal_integral_eq_lintegral_ofReal integrable_radial (ae_of_all _ fun x => f_nonneg _),
    integral_radial]

def H (b : Fin 4 → ℝ) : ENNReal := F (∑ i, b i ^ 2)

/--
@isnad1 id=measurab.0h0v.s5.fc46389d09af from=translated src=- shape=95493978 vocab=fd881a31
-/
theorem measurable_H : Measurable H :=
  measurable_F.comp (by fun_prop)

/--
@isnad1 id=eq.0h0v.s7.07241a3b73a7 from=translated src=- shape=8596fcf6 vocab=c9cd3572
-/
theorem lintegral_H : ∫⁻ b : Fin 4 → ℝ, H b = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  have hmp := PiLp.volume_preserving_ofLp (Fin 4)
  rw [← hmp.lintegral_comp measurable_H, ← lintegral_radial]
  refine lintegral_congr fun x => ?_
  simp only [H]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

end ShellIntegral

end

open ShellIntegral in
/--
@isnad1 id=eq.1h1v.s9.53d606efee1d from=translated src=- shape=cde8ae6f vocab=722c6ff4
-/
theorem solution
    (c : ℝ) (hc : c < 0) :
    ∫⁻ a in {a : Fin 4 → ℝ | a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2) ∈ Set.Icc (1 : ℝ) (Real.exp 2)},
        (ENNReal.ofReal ((a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2)) ^ 2))⁻¹ =
      ENNReal.ofReal (2 * Real.pi ^ 2 / |c|) := by
  classical

  set k : ℝ := Real.sqrt (-c) with hk
  have hkpos : 0 < k := Real.sqrt_pos.2 (by linarith)
  have hk2 : k ^ 2 = -c := Real.sq_sqrt (by linarith)
  set d : Fin 4 → ℝ := ![1, 1, k, k] with hd
  set L : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal d with hL
  have hdetL : L.det = -c := by
    rw [hL, Matrix.det_diagonal, hd]
    simp [Fin.prod_univ_four]
    rw [← sq, hk2]
  have hdetL0 : L.det ≠ 0 := by rw [hdetL]; linarith

  have hν : ∀ a : Fin 4 → ℝ, ∑ i, (Matrix.toLin' L a) i ^ 2 = a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2) := by
    intro a
    simp only [Matrix.toLin'_apply, hL, Matrix.mulVec_diagonal, hd, Fin.sum_univ_four]
    simp
    rw [show k * a 2 = k * a 2 from rfl]
    nlinarith [hk2]
  have hint : (fun a : Fin 4 → ℝ => {a : Fin 4 → ℝ | a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2) ∈
        Set.Icc (1 : ℝ) (Real.exp 2)}.indicator
        (fun a => (ENNReal.ofReal ((a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2)) ^ 2))⁻¹) a) =
      fun a => H (Matrix.toLin' L a) := by
    funext a
    simp only [H, F, hν a, Set.indicator_apply, Set.mem_ofPred_eq]
  have hSm : MeasurableSet {a : Fin 4 → ℝ | a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} :=
    measurableSet_Icc.preimage (by fun_prop)
  rw [← lintegral_indicator hSm, hint,
    ← lintegral_map measurable_H (Matrix.toLin' L).continuous_of_finiteDimensional.measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hdetL0, lintegral_smul_measure, lintegral_H, hdetL,
    abs_inv, abs_neg, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
