import Tengoku.Piirrationalitymeasure.Formalization.LatticeAperiodicity
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientLocalLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The lattice local limit for arbitrary span-one laws with a finite second moment. -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

noncomputable def latticeCenteredCharacteristic (p : PMF ℕ) (q : ℕ) : ℝ → ℂ :=
  charFun (p.toMeasure.map (fun k : ℕ => (k : ℝ) - q))

/--
@isnad1 id=eq.0h3v.s6.b8465a8f30c5 from=translated src=- shape=a82b5b9e vocab=a8762b71
-/
theorem latticeCenteredCharacteristic_eq (p : PMF ℕ) (q : ℕ) (t : ℝ) :
    latticeCenteredCharacteristic p q t =
      charFun (p.toMeasure.map (fun k : ℕ => (k : ℝ))) t *
        Complex.exp (-(q : ℂ) * (t : ℂ) * Complex.I) := by
  have he : (fun k : ℕ => (k : ℝ) - q) =
      (fun x : ℝ => x + -(q : ℝ)) ∘ (fun k : ℕ => (k : ℝ)) := by
    ext k
    simp [sub_eq_add_neg]
  rw [latticeCenteredCharacteristic, he,
    ← Measure.map_map (by fun_prop) (by fun_prop), charFun_map_add_const]
  simp only [RCLike.inner_apply, conj_trivial, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_natCast]
  congr 2
  ring

/--
@isnad1 id=eq.0h3v.s5.672b947d4d88 from=translated src=- shape=08f3bbd4 vocab=7ff7481b
-/
theorem latticeCenteredCharacteristic_norm (p : PMF ℕ) (q : ℕ) (t : ℝ) :
    ‖latticeCenteredCharacteristic p q t‖ =
      ‖charFun (p.toMeasure.map (fun k : ℕ => (k : ℝ))) t‖ := by
  rw [latticeCenteredCharacteristic_eq, norm_mul]
  have he : ‖Complex.exp (-(q : ℂ) * (t : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [he, mul_one]

/--
@isnad1 id=islittle.2h2v.s8.99a0a87533f5 from=translated src=- shape=e3695fca vocab=900e7640
-/
theorem latticeCenteredCharacteristic_taylor (p : PMF ℕ) (q : ℕ)
    (hX : MemLp (fun k : ℕ => (k : ℝ)) 2 p.toMeasure)
    (hmean : ∫ k : ℕ, (k : ℝ) ∂p.toMeasure = q) :
    (fun t : ℝ => latticeCenteredCharacteristic p q t -
      (1 - ((∫ k : ℕ, ((k : ℝ) - q) ^ 2 ∂p.toMeasure : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hc : MemLp (fun k : ℕ => (k : ℝ) - q) 2 p.toMeasure := hX.sub (memLp_const _)
  have hm : ∫ k : ℕ, ((k : ℝ) - q) ∂p.toMeasure = 0 := by
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const _), hmean]
    simp
  exact centered_charFun_taylor hc hm

/--
@isnad1 id=tendsto.4h2v.s8.0995e7c87a15 from=translated src=- shape=44ca02f9 vocab=36304aa5
-/
theorem latticeCenteredCharacteristic_integral_limit (p : PMF ℕ) (q : ℕ)
    (hspan : HasLatticeSpanOne p.support)
    (hX : MemLp (fun k : ℕ => (k : ℝ)) 2 p.toMeasure)
    (hmean : ∫ k : ℕ, (k : ℝ) ∂p.toMeasure = q)
    (hvar : 0 < ∫ k : ℕ, ((k : ℝ) - q) ^ 2 ∂p.toMeasure) :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) *
      ∫ t in -Real.pi..Real.pi, latticeCenteredCharacteristic p q t ^ n) atTop
        (𝓝 (Real.sqrt (2 * Real.pi /
          (∫ k : ℕ, ((k : ℝ) - q) ^ 2 ∂p.toMeasure)) : ℂ)) := by
  have htaylor := latticeCenteredCharacteristic_taylor p q hX hmean
  have hc : Continuous (latticeCenteredCharacteristic p q) := continuous_charFun
  obtain ⟨c, hcpos, hbound⟩ := local_gaussian_global_bound Real.pi_pos
    (div_pos hvar (by norm_num : (0 : ℝ) < 4)) hc.continuousOn
    (fun t ht ht0 => by
      rw [latticeCenteredCharacteristic_norm]
      exact pmf_charFun_norm_strict_of_span_one p hspan (abs_pos.mpr ht0) (abs_le.mpr ht))
    (quadratic_expansion_gaussian_bound hvar htaylor)
  exact gaussian_integral_power_limit Real.pi_pos hcpos hc hbound
    (quadratic_expansion_power_limit htaylor)

/--
@isnad1 id=tendsto.5h3v.s8.cf180766d3c1 from=translated src=- shape=4285802e vocab=bb2dbbc3
-/
theorem lattice_probability_local_limit (p : PMF ℕ) (pn : ℕ → PMF ℕ) (q : ℕ)
    (hspan : HasLatticeSpanOne p.support)
    (hX : MemLp (fun k : ℕ => (k : ℝ)) 2 p.toMeasure)
    (hmean : ∫ k : ℕ, (k : ℝ) ∂p.toMeasure = q)
    (hvar : 0 < ∫ k : ℕ, ((k : ℝ) - q) ^ 2 ∂p.toMeasure)
    (hchar : ∀ (n : ℕ) (t : ℝ),
      charFun ((pn n).toMeasure.map (fun k : ℕ => (k : ℝ))) t =
        charFun (p.toMeasure.map (fun k : ℕ => (k : ℝ))) t ^ n) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * (pn n (q * n)).toReal) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi *
        (∫ k : ℕ, ((k : ℝ) - q) ^ 2 ∂p.toMeasure)))) := by
  have hint (n : ℕ) : (∫ t in -Real.pi..Real.pi,
      latticeCenteredCharacteristic p q t ^ n) =
        (2 * Real.pi : ℂ) * (pn n (q * n)).toReal := by
    have h := lattice_fourier_inversion (pn n) (q * n)
    simp_rw [hchar] at h
    have he (t : ℝ) : latticeCenteredCharacteristic p q t ^ n =
        charFun (p.toMeasure.map (fun k : ℕ => (k : ℝ))) t ^ n *
          Complex.exp (-((q * n : ℕ) : ℂ) * (t : ℂ) * Complex.I) := by
      rw [latticeCenteredCharacteristic_eq, mul_pow, ← Complex.exp_nat_mul]
      congr 1
      congr 1
      push_cast
      ring
    simpa only [← he] using h
  have h := (latticeCenteredCharacteristic_integral_limit p q hspan hX hmean hvar).div_const
    (2 * Real.pi : ℂ)
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
  have h' : Tendsto
      (fun n : ℕ => ((Real.sqrt (n : ℝ) * (pn n (q * n)).toReal : ℝ) : ℂ)) atTop
      (𝓝 ((1 / Real.sqrt (2 * Real.pi *
        (∫ k : ℕ, ((k : ℝ) - q) ^ 2 ∂p.toMeasure)) : ℝ) : ℂ)) := by
    convert! h using 1
    · ext n
      rw [hint]
      push_cast
      field_simp [hpi] <;> ring
    · have hn := congrArg Complex.ofReal
        (gaussian_normalization (∫ k : ℕ, ((k : ℝ) - q) ^ 2 ∂p.toMeasure))
      push_cast at hn
      simpa only [Complex.ofReal_div, Complex.ofReal_one] using congrArg nhds hn.symm
  simpa only [Function.comp_def, Complex.ofReal_re] using (Complex.continuous_re.tendsto _).comp h'

end PiIrrationality
