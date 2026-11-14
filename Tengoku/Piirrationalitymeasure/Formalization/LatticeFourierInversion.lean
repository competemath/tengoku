import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Fourier inversion for a probability mass function on the nonnegative integers. -/

namespace PiIrrationality

open MeasureTheory
open scoped Topology

/--
@isnad1 id=eq.0h1v.s6.bebc00b37e80 from=translated src=- shape=3b8cf03c vocab=10d0bfd5
-/
theorem lattice_frequency_integral (d : ℤ) :
    (∫ t in -Real.pi..Real.pi,
      Complex.exp ((d : ℂ) * (t : ℂ) * Complex.I)) =
        if d = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hd : d = 0
  · subst d
    simp
    ring
  rw [ite_eq_right hd]
  have hc : (d : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hd) Complex.I_ne_zero
  have he (t : ℝ) : (d : ℂ) * (t : ℂ) * Complex.I = ((d : ℂ) * Complex.I) * (t : ℂ) := by
    ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  have hp : Complex.exp ((d : ℂ) * Complex.I * (Real.pi : ℂ)) =
      Complex.exp ((d : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
    rw [show (d : ℂ) * Complex.I * (Real.pi : ℂ) =
        ((d : ℂ) * (Real.pi : ℂ)) * Complex.I by ring,
      show (d : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) =
        (-((d : ℂ) * (Real.pi : ℂ))) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      Complex.sin_int_mul_pi]
    simp
  rw [hp, sub_self, zero_div]

/--
@isnad1 id=eq.0h2v.s7.7e0c114e141a from=translated src=- shape=b52360f3 vocab=20f6c941
-/
theorem lattice_fourier_inversion (p : PMF ℕ) (j : ℕ) :
    (∫ t in -Real.pi..Real.pi,
      charFun (p.toMeasure.map (fun k : ℕ => (k : ℝ))) t *
        Complex.exp (-(j : ℂ) * (t : ℂ) * Complex.I)) =
          (2 * Real.pi : ℂ) * (p j).toReal := by
  let μ := p.toMeasure
  let ν := volume.restrict (Set.Ioc (-Real.pi) Real.pi)
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hint : Integrable
      (fun a : ℝ × ℕ => Complex.exp (((a.2 : ℂ) - (j : ℂ)) * (a.1 : ℂ) * Complex.I))
      (ν.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun a => by simp [Complex.norm_exp])
  have hchar (t : ℝ) : charFun (μ.map (fun k : ℕ => (k : ℝ))) t *
      Complex.exp (-(j : ℂ) * (t : ℂ) * Complex.I) =
        ∫ k : ℕ, Complex.exp (((k : ℂ) - (j : ℂ)) * (t : ℂ) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), ← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun k => by
      dsimp only
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring)
  rw [intervalIntegral.integral_of_le hπ]
  change (∫ t : ℝ, charFun (μ.map (fun k : ℕ => (k : ℝ))) t *
    Complex.exp (-(j : ℂ) * (t : ℂ) * Complex.I) ∂ν) = _
  simp_rw [hchar]
  rw [integral_integral_swap hint]
  have hk (k : ℕ) :
      (∫ t : ℝ, Complex.exp (((k : ℂ) - (j : ℂ)) * (t : ℂ) * Complex.I) ∂ν) =
        if k = j then (2 * Real.pi : ℂ) else 0 := by
    change (∫ t : ℝ in Set.Ioc (-Real.pi) Real.pi,
      Complex.exp (((k : ℂ) - (j : ℂ)) * (t : ℂ) * Complex.I)) = _
    rw [← intervalIntegral.integral_of_le hπ]
    simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero, Int.natCast_inj] using
      lattice_frequency_integral ((k : ℤ) - (j : ℤ))
  simp_rw [hk]
  have hi : (fun k : ℕ => if k = j then (2 * Real.pi : ℂ) else 0) =
      ({j} : Set ℕ).indicator (fun _ => (2 * Real.pi : ℂ)) := by
    ext k
    by_cases hkj : k = j <;> simp [hkj]
  rw [hi, integral_indicator (measurableSet_singleton j), setIntegral_const,
    measureReal_def, PMF.toMeasure_apply_singleton p j (measurableSet_singleton j),
    Complex.real_smul]
  ring

end PiIrrationality
