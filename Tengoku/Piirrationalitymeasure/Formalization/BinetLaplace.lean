import Tengoku.Piirrationalitymeasure.Formalization.BinetRemainder
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Convergent Laplace integrals of the Binet kernel and its finite expansion. -/

namespace PiIrrationality

open MeasureTheory Set

noncomputable def binetLaplace (y : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, Real.exp (-(y * u)) * binetKernel u

theorem integrableOn_pow_mul_exp_neg_mul {y : ℝ} (hy : 0 < y) (m : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ m * Real.exp (-(y * u))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (m : ℝ)) (p := 1)
    (by have := Nat.cast_nonneg (α := ℝ) m; linarith) (by norm_num) hy
  simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using h

theorem integral_pow_mul_exp_neg_mul {y : ℝ} (hy : 0 < y) (m : ℕ) :
    (∫ u : ℝ in Ioi 0, u ^ m * Real.exp (-(y * u))) = (m.factorial : ℝ) / y ^ (m + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ) + 1) (by positivity) hy
  have he : (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) := by norm_num
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [he, Real.rpow_natCast] at h
  simpa only [div_pow, one_pow, one_div, div_eq_mul_inv, mul_one, inv_pow, mul_comm] using h

theorem measurable_binetKernel : Measurable binetKernel := by
  unfold binetKernel
  fun_prop

theorem integrableOn_binetLaplace {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u => Real.exp (-(y * u)) * binetKernel u) (Ioi 0) := by
  have hi := (integrableOn_pow_mul_exp_neg_mul hy 1).div_const 12
  apply hi.mono'
  · exact ((by fun_prop : Measurable (fun u : ℝ => Real.exp (-(y * u)))).mul
      measurable_binetKernel).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (binetKernel_pos hu).le)]
    have h := mul_le_mul_of_nonneg_left (binetKernel_lt_linear hu).le (Real.exp_pos (-(y * u))).le
    simpa only [pow_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

private theorem integral_Ioi_pos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hp : ∀ u : ℝ, 0 < u → 0 < f u) : 0 < ∫ u : ℝ in Ioi 0, f u := by
  have hs : Function.support f ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    exact fun u hu => (hp u hu).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact (hp u hu).le
  · exact hf

theorem binetLaplace_pos {y : ℝ} (hy : 0 < y) : 0 < binetLaplace y := by
  exact integral_Ioi_pos (integrableOn_binetLaplace hy)
    (fun u hu => mul_pos (Real.exp_pos _) (binetKernel_pos hu))

theorem integrableOn_binetKernelApprox {y : ℝ} (hy : 0 < y) (N : ℕ) :
    IntegrableOn (fun u => Real.exp (-(y * u)) * binetKernelApprox u N) (Ioi 0) := by
  simp only [binetKernelApprox, Finset.mul_sum]
  apply integrable_finsetSum
  intro m hm
  convert! (integrableOn_pow_mul_exp_neg_mul hy (2 * m + 1)).const_mul
    ((-1 : ℝ) ^ m * positiveBernoulliCoeff (m + 1)) using 1
  funext u
  ring

noncomputable def binetLaplaceApprox (y : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N,
    (bernoulli (2 * (m + 1)) : ℝ) / ((2 * (m + 1) : ℕ) * y ^ (2 * (m + 1)))

theorem integral_binetKernelApprox {y : ℝ} (hy : 0 < y) (N : ℕ) :
    (∫ u : ℝ in Ioi 0, Real.exp (-(y * u)) * binetKernelApprox u N) =
      binetLaplaceApprox y N := by
  simp only [binetKernelApprox_eq, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    have hf : (fun u : ℝ => Real.exp (-(y * u)) *
        ((bernoulli (2 * (m + 1)) : ℝ) / ((2 * (m + 1)).factorial : ℝ) * u ^ (2 * m + 1))) =
          fun u => ((bernoulli (2 * (m + 1)) : ℝ) / ((2 * (m + 1)).factorial : ℝ)) *
            (u ^ (2 * m + 1) * Real.exp (-(y * u))) := by funext u; ring
    rw [hf, integral_const_mul, integral_pow_mul_exp_neg_mul hy]
    have he : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [he, Nat.factorial_succ]
    push_cast
    field_simp
  · intro m hm
    convert! (integrableOn_pow_mul_exp_neg_mul hy (2 * m + 1)).const_mul
      ((bernoulli (2 * (m + 1)) : ℝ) / ((2 * (m + 1)).factorial : ℝ)) using 1
    funext u
    ring

theorem binetLaplace_remainder_bounds {y : ℝ} (hy : 0 < y) (N : ℕ) :
    0 < (-1 : ℝ) ^ N * (binetLaplace y - binetLaplaceApprox y N) ∧
      (-1 : ℝ) ^ N * (binetLaplace y - binetLaplaceApprox y N) <
        |(bernoulli (2 * (N + 1)) : ℝ)| /
          ((2 * (N + 1) : ℕ) * y ^ (2 * (N + 1))) := by
  let R : ℝ → ℝ := fun u => Real.exp (-(y * u)) *
    ((-1 : ℝ) ^ N * (binetKernel u - binetKernelApprox u N))
  let U : ℝ → ℝ := fun u => positiveBernoulliCoeff (N + 1) *
    (u ^ (2 * N + 1) * Real.exp (-(y * u)))
  have hiK := integrableOn_binetLaplace hy
  have hiP := integrableOn_binetKernelApprox hy N
  have hR : IntegrableOn R (Ioi 0) := by
    have hS : IntegrableOn (fun u => (-1 : ℝ) ^ N *
        (Real.exp (-(y * u)) * binetKernel u -
          Real.exp (-(y * u)) * binetKernelApprox u N)) (Ioi 0) :=
      (hiK.sub hiP).const_mul ((-1 : ℝ) ^ N)
    exact hS.congr_fun (fun u _ => by dsimp [R]; ring) measurableSet_Ioi
  have hU : IntegrableOn U (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_mul hy (2 * N + 1)).const_mul _
  have heR : (∫ u : ℝ in Ioi 0, R u) =
      (-1 : ℝ) ^ N * (binetLaplace y - binetLaplaceApprox y N) := by
    have he : R = fun u => (-1 : ℝ) ^ N *
        (Real.exp (-(y * u)) * binetKernel u -
          Real.exp (-(y * u)) * binetKernelApprox u N) := by
      funext u
      dsimp [R]
      ring
    rw [he, integral_const_mul, integral_sub hiK hiP, integral_binetKernelApprox hy]
    rfl
  have heU : (∫ u : ℝ in Ioi 0, U u) =
      |(bernoulli (2 * (N + 1)) : ℝ)| / ((2 * (N + 1) : ℕ) * y ^ (2 * (N + 1))) := by
    rw [show U = fun u => positiveBernoulliCoeff (N + 1) *
      (u ^ (2 * N + 1) * Real.exp (-(y * u))) from rfl,
      integral_const_mul, integral_pow_mul_exp_neg_mul hy,
      positiveBernoulliCoeff_eq_abs (Nat.succ_pos N)]
    have he : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [he, Nat.factorial_succ]
    push_cast
    field_simp
  have hp := integral_Ioi_pos hR (fun u hu =>
    mul_pos (Real.exp_pos _) (binetKernel_remainder_bounds hu N).1)
  have hd := integral_Ioi_pos (hU.sub hR) (fun u hu => by
    have h := mul_lt_mul_of_pos_left (binetKernel_remainder_bounds hu N).2
      (Real.exp_pos (-(y * u)))
    dsimp [U, R]
    nlinarith)
  simp only [Pi.sub_apply] at hd
  rw [integral_sub hU hR, heU, heR] at hd
  rw [heR] at hp
  exact ⟨hp, by linarith⟩

theorem binetLaplace_remainder_abs_lt {y : ℝ} (hy : 0 < y) (N : ℕ) :
    |binetLaplace y - binetLaplaceApprox y N| <
      |(bernoulli (2 * (N + 1)) : ℝ)| /
        ((2 * (N + 1) : ℕ) * y ^ (2 * (N + 1))) := by
  have h := binetLaplace_remainder_bounds hy N
  have he : |binetLaplace y - binetLaplaceApprox y N| =
      (-1 : ℝ) ^ N * (binetLaplace y - binetLaplaceApprox y N) := by
    calc
      _ = |(-1 : ℝ) ^ N * (binetLaplace y - binetLaplaceApprox y N)| := by simp [abs_mul]
      _ = _ := abs_of_pos h.1
  rw [he]
  exact h.2

theorem binetLaplace_lt_inv_sq {y : ℝ} (hy : 0 < y) :
    binetLaplace y < 1 / (12 * y ^ 2) := by
  have h := (binetLaplace_remainder_bounds hy 0).2
  norm_num [binetLaplaceApprox, bernoulli_eq_bernoulli'_of_ne_one] at h
  convert! h using 1
  ring

end PiIrrationality
