import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.CurvatureIntegrals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The probability kernels used in Appendix A and their mixed quadratic integral. -/

open MeasureTheory Set Filter
open scoped Topology

namespace EntropyConstrainedMissingMass
namespace Curvature

/-- The probability kernel of scale `a`.-/
noncomputable def kernel (a s : ℝ) : ℝ := 2 * a ^ 2 / (s + a) ^ 3

/-- Appendix A's mixed quadratic kernel integral.-/
noncomputable def J (a : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (s - 1) ^ 2 * kernel 1 s * kernel a s

/-- The kernel has total mass one.
@isnad1 id=eq.1h1v.s5.be18cfccb7ed from=translated src=- shape=3e8753af vocab=c4509bbb
-/
theorem integral_kernel (a : ℝ) (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), kernel a s) = 1 := by
  have heq : kernel a = fun s : ℝ => (2 * a ^ 2) * (1 / (s + a) ^ 3) := by
    funext s
    simp [kernel, div_eq_mul_inv]
  rw [heq, integral_const_mul, integral_inv_add_pow a ha 1]
  norm_num
  field_simp

/-- The kernel's mean is its scale.
@isnad1 id=eq.1h1v.s5.639be7c208d5 from=translated src=- shape=c490cb9a vocab=d1a8b738
-/
theorem integral_mul_kernel (a : ℝ) (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), s * kernel a s) = a := by
  have heq : (fun s : ℝ => s * kernel a s) =
      fun s : ℝ => (2 * a ^ 2) * (s / D a a a s) := by
    funext s
    rw [D_uniform]
    simp [kernel]
    ring
  rw [heq, integral_const_mul]
  change (2 * a ^ 2) * I1 a a a = a
  rw [I1_uniform a ha]
  field_simp

/-- The mixed kernel integral at the uniform scale.
@isnad1 id=eq.0h0v.s5.c94251ca5703 from=translated src=- shape=d4f6e56f vocab=7fc6b6ac
-/
theorem J_one : J 1 = 8 / 15 := by
  have heq : (fun s : ℝ => (s - 1) ^ 2 * kernel 1 s * kernel 1 s) =
      fun s : ℝ => 4 * ((s - 1) ^ 2 / ((s + 1) ^ 3) ^ 2) := by
    funext s
    simp only [kernel, one_pow, mul_one, div_eq_mul_inv, ← inv_pow]
    ring
  unfold J
  rw [heq, integral_const_mul, integral_uniform_curvature_numerator 1 (by norm_num)]
  norm_num

/-- The convergent difference of two reciprocal kernels integrates to a logarithm.
@isnad1 id=and.1h1v.s7.c6c375199e43 from=translated src=- shape=f40709a6 vocab=bb7d07ca
-/
theorem integral_reciprocal_difference (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => 1 / (s + 1) - 1 / (s + a)) (Ioi (0 : ℝ)) ∧
      (∫ s in Ioi (0 : ℝ), (1 / (s + 1) - 1 / (s + a))) = Real.log a := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt
      (fun v : ℝ => Real.log (v + 1) - Real.log (v + a))
      (1 / (s + 1) - 1 / (s + a)) s := by
    intro s hs
    have hs1 : s + 1 ≠ 0 := by linarith [mem_Ici.mp hs]
    have hsa : s + a ≠ 0 := by linarith [mem_Ici.mp hs]
    simpa using (((hasDerivAt_id s).add_const 1).log hs1).fun_sub
      (((hasDerivAt_id s).add_const a).log hsa)
  have hinv : Tendsto (fun s : ℝ => (s + a)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ a tendsto_id)
  have hrat : Tendsto (fun s : ℝ => 1 + (1 - a) * (s + a)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hrat
  have ht : Tendsto (fun s : ℝ => Real.log (s + 1) - Real.log (s + a)) atTop (𝓝 0) := by
    have hfun : (fun s : ℝ => Real.log (1 + (1 - a) * (s + a)⁻¹)) =ᶠ[atTop]
        (fun s : ℝ => Real.log (s + 1) - Real.log (s + a)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      have hsa : s + a ≠ 0 := by linarith
      have hs1 : s + 1 ≠ 0 := by linarith
      have hrat_eq : 1 + (1 - a) * (s + a)⁻¹ = (s + 1) / (s + a) := by
        field_simp
        ring
      rw [hrat_eq, Real.log_div hs1 hsa]
    simpa using hlog.congr' hfun
  have hi : IntegrableOn (fun s : ℝ => 1 / (s + 1) - 1 / (s + a)) (Ioi (0 : ℝ)) := by
    by_cases h1a : 1 ≤ a
    · apply integrableOn_Ioi_deriv_of_nonneg' hd _ ht
      intro s hs
      have hp : 0 < s + 1 := by linarith [mem_Ioi.mp hs]
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hp (by linarith))
    · apply integrableOn_Ioi_deriv_of_nonpos' hd _ ht
      intro s hs
      have hp : 0 < s + a := by linarith [mem_Ioi.mp hs]
      exact sub_nonpos.mpr (one_div_le_one_div_of_le hp (by linarith))
  refine ⟨hi, ?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht

/-- The partial-fraction identity underlying the closed form of `J`.
@isnad1 id=eq.3h2v.s9.5c26b184d408 from=translated src=- shape=91d6155b vocab=9f3387b7
-/
theorem kernel_integrand_partial_fraction (a s : ℝ) (ha : a ≠ 1)
    (hs1 : s + 1 ≠ 0) (hsa : s + a ≠ 0) :
    (s - 1) ^ 2 * kernel 1 s * kernel a s =
      (16 * a ^ 2 / (a - 1) ^ 3) * (1 / (s + 1) ^ 3) -
      (4 * a ^ 2 * (a + 1) ^ 2 / (a - 1) ^ 3) * (1 / (s + a) ^ 3) -
      (16 * a ^ 2 * (a + 2) / (a - 1) ^ 4) * (1 / (s + 1) ^ 2) -
      (4 * a ^ 2 * (a + 1) * (a + 5) / (a - 1) ^ 4) * (1 / (s + a) ^ 2) +
      (4 * a ^ 2 * (a ^ 2 + 10 * a + 13) / (a - 1) ^ 5) *
        (1 / (s + 1) - 1 / (s + a)) := by
  have ham : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  unfold kernel
  field_simp
  ring

/-- The nonuniform mixed integral is convergent and has the exact logarithmic
closed form printed in Appendix A. Simple-pole terms are integrated as a
convergent difference, rather than individually.
@isnad1 id=and.2h1v.s8.cdb436908331 from=translated src=- shape=3c036d00 vocab=e8d31e81
-/
theorem J_closed_form_aux (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    IntegrableOn (fun s : ℝ => (s - 1) ^ 2 * kernel 1 s * kernel a s) (Ioi (0 : ℝ)) ∧
      J a = (4 * a ^ 2 * (a ^ 2 + 10 * a + 13) * Real.log a -
        2 * (a - 1) * (7 * a ^ 3 + 33 * a ^ 2 + 9 * a - 1)) / (a - 1) ^ 5 := by
  let A3 : ℝ := 16 * a ^ 2 / (a - 1) ^ 3
  let B3 : ℝ := 4 * a ^ 2 * (a + 1) ^ 2 / (a - 1) ^ 3
  let A2 : ℝ := 16 * a ^ 2 * (a + 2) / (a - 1) ^ 4
  let B2 : ℝ := 4 * a ^ 2 * (a + 1) * (a + 5) / (a - 1) ^ 4
  let L : ℝ := 4 * a ^ 2 * (a ^ 2 + 10 * a + 13) / (a - 1) ^ 5
  let f : ℝ → ℝ := fun s => A3 * (1 / (s + 1) ^ 3) - B3 * (1 / (s + a) ^ 3) -
    A2 * (1 / (s + 1) ^ 2) - B2 * (1 / (s + a) ^ 2) +
      L * (1 / (s + 1) - 1 / (s + a))
  have hEq : ∀ s ∈ Ioi (0 : ℝ), (s - 1) ^ 2 * kernel 1 s * kernel a s = f s := by
    intro s hs
    exact kernel_integrand_partial_fraction a s ha1
      (by linarith [mem_Ioi.mp hs]) (by linarith [mem_Ioi.mp hs])
  have h13 : IntegrableOn (fun s : ℝ => A3 * (1 / (s + 1) ^ 3)) (Ioi (0 : ℝ)) :=
    (integrableOn_inv_add_pow 1 (by norm_num) 1).const_mul A3
  have ha3 : IntegrableOn (fun s : ℝ => B3 * (1 / (s + a) ^ 3)) (Ioi (0 : ℝ)) :=
    (integrableOn_inv_add_pow a ha 1).const_mul B3
  have h12 : IntegrableOn (fun s : ℝ => A2 * (1 / (s + 1) ^ 2)) (Ioi (0 : ℝ)) :=
    (integrableOn_inv_add_pow 1 (by norm_num) 0).const_mul A2
  have ha2 : IntegrableOn (fun s : ℝ => B2 * (1 / (s + a) ^ 2)) (Ioi (0 : ℝ)) :=
    (integrableOn_inv_add_pow a ha 0).const_mul B2
  have hl : IntegrableOn (fun s : ℝ => L * (1 / (s + 1) - 1 / (s + a))) (Ioi (0 : ℝ)) :=
    (integral_reciprocal_difference a ha).1.const_mul L
  have hf : IntegrableOn f (Ioi (0 : ℝ)) :=
    (((h13.fun_sub ha3).fun_sub h12).fun_sub ha2).fun_add hl
  refine ⟨hf.congr_fun (fun s hs => (hEq s hs).symm) measurableSet_Ioi, ?_⟩
  have hiEq : J a = ∫ s in Ioi (0 : ℝ), f s :=
    setIntegral_congr_fun measurableSet_Ioi hEq
  rw [hiEq]
  dsimp only [f]
  rw [integral_add (((h13.fun_sub ha3).fun_sub h12).fun_sub ha2) hl,
    integral_sub ((h13.fun_sub ha3).fun_sub h12) ha2,
    integral_sub (h13.fun_sub ha3) h12, integral_sub h13 ha3]
  simp only [integral_const_mul]
  rw [integral_inv_add_pow 1 (by norm_num) 1, integral_inv_add_pow a ha 1,
    integral_inv_add_pow 1 (by norm_num) 0, integral_inv_add_pow a ha 0,
    (integral_reciprocal_difference a ha).2]
  dsimp [A3, B3, A2, B2, L]
  have ham : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  norm_num
  field_simp
  ring

/-- Closed form for a scale different from one.
@isnad1 id=eq.2h1v.s8.4c7a1a5500d7 from=translated src=- shape=d1870f7d vocab=df61f2a5
-/
theorem J_closed_form (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    J a = (4 * a ^ 2 * (a ^ 2 + 10 * a + 13) * Real.log a -
      2 * (a - 1) * (7 * a ^ 3 + 33 * a ^ 2 + 9 * a - 1)) / (a - 1) ^ 5 :=
  (J_closed_form_aux a ha ha1).2

/-- Convergence of the mixed kernel integral for every positive scale.
@isnad1 id=integrab.1h1v.s6.4900a0deb34d from=translated src=- shape=82e7f4f6 vocab=0cfe0e8f
-/
theorem integrableOn_J (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => (s - 1) ^ 2 * kernel 1 s * kernel a s) (Ioi (0 : ℝ)) := by
  by_cases ha1 : a = 1
  · subst a
    have hu : IntegrableOn (fun s : ℝ => 4 * ((s - 1) ^ 2 / (D 1 1 1 s) ^ 2))
        (Ioi (0 : ℝ)) :=
      (integrableOn_curvature_numerator 1 1 1 1 (by norm_num) (by norm_num)
        (by norm_num)).const_mul 4
    refine hu.congr_fun (fun s hs => ?_) measurableSet_Ioi
    dsimp only
    rw [D_uniform]
    simp only [kernel, one_pow, mul_one, div_eq_mul_inv, ← inv_pow]
    ring
  · exact (J_closed_form_aux a ha ha1).1

/-- The sharp kernel bound holds with equality at the uniform scale.
@isnad1 id=eq.0h0v.s6.9299e432964a from=translated src=- shape=a980d0a2 vocab=b78c5dc0
-/
theorem kernel_bound_one : J 1 = 2 * (9 - (1 : ℝ)) / (15 * (1 + 1)) := by
  rw [J_one]
  norm_num

/-- The cubic appearing in the positive remainder is positive on positive arguments.
@isnad1 id=lt.1h1v.s7.1661467f6729 from=translated src=- shape=5d755901 vocab=5233fd79
-/
theorem kernel_remainder_cubic_pos (b : ℝ) (hb : 0 < b) :
    0 < 2 * b ^ 3 + 12 * b ^ 2 - 10 * b + 13 := by
  have hsq := sq_nonneg (b - 5 / 12)
  have hc : 0 < b ^ 3 := pow_pos hb 3
  nlinarith

private noncomputable def remainderPrimitive (a b : ℝ) : ℝ :=
    ((-1 / 3 : ℝ)) * b ^ 6 +
    (2 * (a - 1)) * b ^ 5 +
    (-(10 * a ^ 2 - 25 * a - 11) / 2) * b ^ 4 +
    ((20 * a ^ 3 - 100 * a ^ 2 - 110 * a - 23) / 3) * b ^ 3 +
    ((-10 * a ^ 4 + 100 * a ^ 3 + 220 * a ^ 2 + 115 * a + 13) / 2) * b ^ 2 +
    (a * (2 * a ^ 4 - 50 * a ^ 3 - 220 * a ^ 2 - 230 * a - 65)) * b +
    (10 * a ^ 2 * (a + 1) * (a ^ 2 + 10 * a + 13)) * Real.log b +
    (a ^ 3 * (22 * a ^ 2 + 115 * a + 130)) * b⁻¹ +
    (-a ^ 4 * (23 * a + 65) / 2) * (b⁻¹) ^ 2 +
    (13 * a ^ 5 / 3) * (b⁻¹) ^ 3

/-- The nonnegative density in Appendix A's exact remainder.-/
noncomputable def kernelRemainderDensity (a v : ℝ) : ℝ :=
  let b := 1 + v * (a - 1)
  v * (1 - v) ^ 5 * (2 * b ^ 3 + 12 * b ^ 2 - 10 * b + 13) / b ^ 4

private theorem affine_scale_pos (a v : ℝ) (ha : 0 < a) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < 1 + v * (a - 1) := by
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
    have hva := mul_pos hvpos ha
    nlinarith [hv.2]

/-- The remainder density is continuous across the whole unit interval.
@isnad1 id=continuo.1h1v.s5.bf3646a69463 from=translated src=- shape=4756762a vocab=6cee50e5
-/
theorem continuousOn_kernelRemainderDensity (a : ℝ) (ha : 0 < a) :
    ContinuousOn (kernelRemainderDensity a) (Icc (0 : ℝ) 1) := by
  unfold kernelRemainderDensity
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro v hv
    exact pow_ne_zero _ (ne_of_gt (affine_scale_pos a v ha hv))

/-- Nonnegativity of the remainder density.
@isnad1 id=le.2h2v.s5.018916a827eb from=translated src=- shape=341d216e vocab=729300f0
-/
theorem kernelRemainderDensity_nonneg (a v : ℝ) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) 1) : 0 ≤ kernelRemainderDensity a v := by
  have hb := affine_scale_pos a v ha hv
  have hpoly := kernel_remainder_cubic_pos _ hb
  unfold kernelRemainderDensity
  exact div_nonneg (mul_nonneg (mul_nonneg hv.1 (pow_nonneg (by linarith [hv.2]) 5))
    (le_of_lt hpoly)) (le_of_lt (pow_pos hb 4))

/-- The remainder integral is strictly positive for every positive scale.
@isnad1 id=lt.1h1v.s5.be5a3a6514ce from=translated src=- shape=f628c7bb vocab=293e3c60
-/
theorem integral_kernelRemainderDensity_pos (a : ℝ) (ha : 0 < a) :
    0 < ∫ v in (0 : ℝ)..1, kernelRemainderDensity a v := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuousOn_kernelRemainderDensity a ha).intervalIntegrable_of_Icc (by norm_num))
    _ (by norm_num)
  intro v hv
  have hb := affine_scale_pos a v ha ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have hpoly := kernel_remainder_cubic_pos _ hb
  unfold kernelRemainderDensity
  exact div_pos (mul_pos (mul_pos hv.1 (pow_pos (by linarith [hv.2]) 5))
    hpoly) (pow_pos hb 4)

end Curvature
end EntropyConstrainedMissingMass
