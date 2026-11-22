import Tengoku.Leancert.LeanCert.Analysis.DBN.HeatFlow
import Tengoku.Leancert.LeanCert.Analysis.ParametricIntegral
import Tengoku.Leancert.LeanCert.Analysis.GaussianMoments
import Tengoku.Seed.Analysis.Complex.RealDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Polynomial moments with cosine phase shifts. Successive phase shifts
encode spatial derivatives without a separate sine/cosine proof hierarchy. -/
namespace LeanCert.Analysis.DBN
open MeasureTheory Set Filter
open scoped Topology

noncomputable def momentIntegrand (m : ℕ) (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ)^m * ((Real.exp (t*u^2)*Phi u : ℝ) : ℂ) *
    Complex.cos (z*(u : ℂ)+(m : ℂ)*(Real.pi : ℂ)/2)

noncomputable def moment (m : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), momentIntegrand m t z u

/--
@isnad1 id=eq.0h3v.s4.8839114c7738 from=translated src=- shape=8534e31c vocab=1358e642
-/
@[simp] theorem momentIntegrand_zero (t : ℝ) (z : ℂ) (u : ℝ) :
    momentIntegrand 0 t z u = heatIntegrand t z u := by simp [momentIntegrand, heatIntegrand]

/--
@isnad1 id=eq.0h2v.s4.e05d38a13195 from=translated src=- shape=50c785e6 vocab=6bb8f5e9
-/
@[simp] theorem moment_zero (t : ℝ) (z : ℂ) : moment 0 t z = H t z := by
  simp [moment, H]

/--
@isnad1 id=measurab.0h3v.s3.f37ca969c85f from=translated src=- shape=618fe02e vocab=cf833906
-/
theorem measurable_momentIntegrand (m : ℕ) (t : ℝ) (z : ℂ) :
    Measurable (momentIntegrand m t z) := by
  unfold momentIntegrand
  have hp := measurable_Phi
  fun_prop

/--
@isnad1 id=le.1h4v.s6.5a849aeadcde from=translated src=- shape=ffac6178 vocab=e023f3fc
-/
theorem momentIntegrand_bound (m : ℕ) (t : ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖momentIntegrand m t z u‖ ≤ heatMajorant t z * (u^m * Real.exp (-u^2)) := by
  have hc := norm_cos_le_exp_abs_im (z*(u : ℂ)+(m : ℂ)*(Real.pi : ℂ)/2)
  have he : (z*(u : ℂ)+(m : ℂ)*(Real.pi : ℂ)/2).im = z.im*u := by
    simp [Complex.mul_im]
  rw [he, abs_mul, abs_of_nonneg hu] at hc
  have h := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ u^m * (Real.exp (t*u^2)*‖Phi u‖) by positivity)
  have hn : ‖momentIntegrand m t z u‖ =
      u^m * (Real.exp (t*u^2)*‖Phi u‖) *
        ‖Complex.cos (z*(u : ℂ)+(m : ℂ)*(Real.pi : ℂ)/2)‖ := by
    simp only [momentIntegrand, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu, abs_of_pos (Real.exp_pos _)]
  rw [← hn] at h
  apply h.trans
  have h' := mul_le_mul_of_nonneg_left (heat_weight_bound t z hu) (show 0 ≤ u^m by positivity)
  nlinarith

/--
@isnad1 id=integrab.0h3v.s5.1d2bd4b94a16 from=translated src=- shape=d50092d3 vocab=a9f74339
-/
theorem momentIntegrand_integrable (m : ℕ) (t : ℝ) (z : ℂ) :
    IntegrableOn (momentIntegrand m t z) (Ioi 0) := by
  apply ((integrableOn_gaussian_moment m).const_mul (heatMajorant t z)).mono'
    (measurable_momentIntegrand m t z).aestronglyMeasurable
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun u hu => momentIntegrand_bound m t z hu.le)

/--
@isnad1 id=continuo.0h0v.s5.75a06eeb3c1b from=translated src=- shape=82943330 vocab=68807ecd
-/
theorem continuous_heatMajorant : Continuous (fun p : ℝ × ℂ => heatMajorant p.1 p.2) := by
  unfold heatMajorant
  fun_prop

/-- Joint continuity, also for the spatial derivative moments.
@isnad1 id=continuo.0h1v.s5.81866c67772c from=translated src=- shape=5eecb333 vocab=674a4bf8
-/
theorem continuous_moment (m : ℕ) : Continuous (fun p : ℝ × ℂ => moment m p.1 p.2) := by
  apply ParametricIntegral.continuous_integral
    (fun (p : ℝ × ℂ) u => momentIntegrand m p.1 p.2 u) (fun (p : ℝ × ℂ) => heatMajorant p.1 p.2)
    (fun u : ℝ => u^m*Real.exp (-u^2)) continuous_heatMajorant (integrableOn_gaussian_moment m)
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => mul_nonneg (pow_nonneg hu.le _) (Real.exp_pos _).le)
  · intro p
    exact (measurable_momentIntegrand m p.1 p.2).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu p => momentIntegrand_bound m p.1 p.2 hu.le)
  · apply Eventually.of_forall
    intro u
    unfold momentIntegrand
    fun_prop

/--
@isnad1 id=hasderiv.0h4v.s6.ce2903f0ef53 from=translated src=- shape=068f76ee vocab=9fcb5b2e
-/
theorem hasDerivAt_momentIntegrand_z (m : ℕ) (t u : ℝ) (z : ℂ) :
    HasDerivAt (fun w => momentIntegrand m t w u) (momentIntegrand (m+1) t z u) z := by
  have hd := ((Complex.hasDerivAt_cos (z*(u : ℂ)+(m : ℂ)*(Real.pi : ℂ)/2)).comp z
    (((hasDerivAt_id z).mul_const (u : ℂ)).add_const ((m : ℂ)*(Real.pi : ℂ)/2))).const_mul
      ((u : ℂ)^m * ((Real.exp (t*u^2)*Phi u : ℝ) : ℂ))
  convert! hd using 1
  unfold momentIntegrand
  push_cast
  rw [show z*(u : ℂ)+((m : ℂ)+1)*(Real.pi : ℂ)/2 =
    (z*(u : ℂ)+(m : ℂ)*(Real.pi : ℂ)/2)+(Real.pi : ℂ)/2 by ring,
    Complex.cos_add_pi_div_two, pow_succ]
  ring

/-- Every spatial derivative can be passed through the defining integral.
@isnad1 id=hasderiv.0h3v.s5.6bf9b8e32233 from=translated src=- shape=a72c68f5 vocab=42a30aba
-/
theorem hasDerivAt_moment_z (m : ℕ) (t : ℝ) (z : ℂ) :
    HasDerivAt (moment m t) (moment (m+1) t z) z := by
  apply (ParametricIntegral.hasDerivAt_integral
    (fun w u => momentIntegrand m t w u) (fun w u => momentIntegrand (m+1) t w u)
    (fun w => heatMajorant t w) (fun u : ℝ => u^(m+1)*Real.exp (-u^2))
    (by unfold heatMajorant; fun_prop) (integrableOn_gaussian_moment (m+1)) _
    (fun w => (measurable_momentIntegrand m t w).aestronglyMeasurable)
    (fun w => (measurable_momentIntegrand (m+1) t w).aestronglyMeasurable) _ _ z
    (momentIntegrand_integrable m t z)).2
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => mul_nonneg (pow_nonneg hu.le _) (Real.exp_pos _).le)
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu w => momentIntegrand_bound (m+1) t w hu.le)
  · exact Eventually.of_forall fun u w => hasDerivAt_momentIntegrand_z m t u w

end LeanCert.Analysis.DBN
