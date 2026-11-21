import Tengoku.PshdLean.PshLines.RegularDistribution
import Tengoku.PshdLean.PshLines.LeviForm
import Tengoku.Seed.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Classical derivatives as distributional derivatives

For a finite-dimensional real normed space with a Haar measure, integration
by parts against actual compactly supported test functions identifies the
derivatives of regular distributions with their classical densities.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

namespace PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Opens E}

/-- At infinite test-function order the bundled directional derivative is the
classical Fréchet derivative evaluated on the direction.
@isnad1 id=eq.0h5v.s10.357bb5ec9ddc from=translated src=- shape=fff39451 vocab=7ca56e69
-/
theorem testFunction_lineDerivCLM_apply_eq_fderiv (φ : 𝓓(Ω, ℝ)) (v x : E) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ x = fderiv ℝ φ x v := by
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le φ (by simp)]

/-- A constant-direction derivative of a C² function is C¹.
@isnad1 id=contdiff.1h3v.s8.e9612ac2af1f from=translated src=- shape=468061cb vocab=87b18e64
-/
theorem contDiff_fderiv_apply_of_two {u : E → ℝ} (hu : ContDiff ℝ 2 u) (v : E) :
    ContDiff ℝ 1 (fun x => fderiv ℝ u x v) :=
  (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- Differentiating the first directional derivative gives the actual
Fréchet Hessian, in the indicated order of its arguments.
@isnad1 id=eq.1h5v.s9.0e0570a699c6 from=translated src=- shape=88ba3c5d vocab=75d4d6a8
-/
theorem fderiv_fderiv_apply_eq_realHessian {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ u y w) x v = realHessian u x v w := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hD (differentiableAt_const w)]
  simp [realHessian_eq_fderiv]

/--
@isnad1 id=continuo.1h4v.s6.f8fbb54ce310 from=translated src=- shape=620e3743 vocab=55ee9ec8
-/
theorem continuous_realHessian {u : E → ℝ} (hu : ContDiff ℝ 2 u) (v w : E) :
    Continuous (fun x => realHessian u x v w) := by
  have hD : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have h : Continuous (fun x => fderiv ℝ (fderiv ℝ u) x v w) :=
    (hD.clm_apply continuous_const).clm_apply continuous_const
  simpa only [realHessian_eq_fderiv] using h

/--
@isnad1 id=continuo.1h3v.s6.b0e496b1863b from=translated src=- shape=039ddd81 vocab=ce2df1f7
-/
theorem continuous_leviForm [NormedSpace ℂ E] {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (v : E) : Continuous (fun x => leviForm u x v) := by
  exact ((continuous_realHessian hu v v).add
    (continuous_realHessian hu (Complex.I • v) (Complex.I • v))).div_const 4

section Haar

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- Continuous differentiability supplies the local integrability of each
directional derivative; this is not an extra density hypothesis.
@isnad1 id=locallyi.1h5v.s8.c95791d9762e from=translated src=- shape=d2e4fbd5 vocab=34bbc4fc
-/
theorem locallyIntegrableOn_fderiv_of_contDiff {u : E → ℝ}
    (hu : ContDiff ℝ 1 u) (v : E) :
    LocallyIntegrableOn (fun x => fderiv ℝ u x v) Ω μ :=
  ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).locallyIntegrable
    |>.locallyIntegrableOn Ω

/-- The distributional directional derivative of a C¹ density is its actual
classical directional derivative. All derivative orders are explicitly `⊤`.
@isnad1 id=eq.1h5v.s11.5776ac34fb10 from=translated src=- shape=f7888991 vocab=bf19d1e1
-/
theorem lineDerivCLM_regularDistribution {u : E → ℝ}
    (hu : ContDiff ℝ 1 u) (v : E) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v
        (regularDistribution μ u (hu.continuous.locallyIntegrable.locallyIntegrableOn Ω)) =
      regularDistribution μ (fun x => fderiv ℝ u x v)
        (locallyIntegrableOn_fderiv_of_contDiff hu v) := by
  ext φ
  have huL : LocallyIntegrableOn u Ω μ :=
    hu.continuous.locallyIntegrable.locallyIntegrableOn Ω
  have hduL : LocallyIntegrableOn (fun x => fderiv ℝ u x v) Ω μ :=
    locallyIntegrableOn_fderiv_of_contDiff hu v
  let ψ : 𝓓(Ω, ℝ) := TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ
  have hψ : ∀ x, ψ x = fderiv ℝ φ x v :=
    fun x => testFunction_lineDerivCLM_apply_eq_fderiv φ v x
  have hψu : Integrable (fun x => ψ x * u x) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) huL ψ
  have hdφu : Integrable (fun x => fderiv ℝ φ x v * u x) μ := by
    simpa only [hψ] using hψu
  have hφdu : Integrable (fun x => φ x * fderiv ℝ u x v) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hduL φ
  have hφu : Integrable (fun x => φ x * u x) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) huL φ
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdφu hφdu hφu
    (fun x _ => φ.contDiff.differentiable (by simp) x)
    (fun x _ => hu.differentiable (by norm_num) x)
  rw [Distribution.lineDerivCLM_apply, regularDistribution_apply, regularDistribution_apply]
  simpa only [testFunction_lineDerivCLM_apply_eq_fderiv] using hibp.symm

/-- Two distributional derivatives of a C² density have its real Hessian as
their regular density.
@isnad1 id=eq.1h6v.s12.19991f2e0f89 from=translated src=- shape=37a021b6 vocab=89e699c2
-/
theorem lineDerivCLM_lineDerivCLM_regularDistribution {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (v w : E) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w
        (regularDistribution μ u (hu.continuous.locallyIntegrable.locallyIntegrableOn Ω))) =
      regularDistribution μ (fun x => realHessian u x v w)
        ((continuous_realHessian hu v w).locallyIntegrable.locallyIntegrableOn Ω) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hdu : ContDiff ℝ 1 (fun x => fderiv ℝ u x w) :=
    contDiff_fderiv_apply_of_two hu w
  rw [lineDerivCLM_regularDistribution hu1 w, lineDerivCLM_regularDistribution hdu v]
  exact regularDistribution_congr_ae
    (locallyIntegrableOn_fderiv_of_contDiff hdu v)
    ((continuous_realHessian hu v w).locallyIntegrable.locallyIntegrableOn Ω)
    (Filter.Eventually.of_forall (fun x => fderiv_fderiv_apply_eq_realHessian hu x v w))

variable [NormedSpace ℂ E]

/-- The classical C² Levi form defines a locally integrable density.
@isnad1 id=locallyi.1h5v.s7.7a861a085158 from=translated src=- shape=206d8b57 vocab=fce9d8b8
-/
theorem locallyIntegrableOn_leviForm_of_contDiff {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (v : E) :
    LocallyIntegrableOn (fun x => leviForm u x v) Ω μ :=
  (continuous_leviForm hu v).locallyIntegrable.locallyIntegrableOn Ω

/-- The distributional Levi operator agrees with the regular distribution
whose density is the classical Levi form, with the same factor one quarter.
@isnad1 id=eq.1h5v.s11.d68abfdce4d8 from=translated src=- shape=477bdd6f vocab=a48f5051
-/
theorem distributionalLeviCLM_regularDistribution {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (v : E) :
    distributionalLeviCLM v
        (regularDistribution μ u (hu.continuous.locallyIntegrable.locallyIntegrableOn Ω)) =
      regularDistribution μ (fun x => leviForm u x v)
        (locallyIntegrableOn_leviForm_of_contDiff hu v) := by
  ext φ
  simp only [distributionalLeviCLM, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [lineDerivCLM_lineDerivCLM_regularDistribution hu v v,
    lineDerivCLM_lineDerivCLM_regularDistribution hu (Complex.I • v) (Complex.I • v)]
  simp only [regularDistribution_apply]
  have hA : Integrable (fun x => φ x * realHessian u x v v) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      ((continuous_realHessian hu v v).locallyIntegrable.locallyIntegrableOn Ω) φ
  have hB : Integrable
      (fun x => φ x * realHessian u x (Complex.I • v) (Complex.I • v)) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      ((continuous_realHessian hu (Complex.I • v) (Complex.I • v)).locallyIntegrable
        |>.locallyIntegrableOn Ω) φ
  rw [← integral_add hA hB, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp only [leviForm]; ring)

/-- A nonnegative classical Levi form on the test-function domain produces
nonnegative Levi distributions. No sign condition outside that domain is
needed, because the test functions vanish there.
@isnad1 id=hasnonne.2h4v.s7.95760282e655 from=translated src=- shape=46cef901 vocab=a166bb7a
-/
theorem hasNonnegativeDistributionalLevi_regularDistribution {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hL : ∀ x ∈ Ω, ∀ v : E, 0 ≤ leviForm u x v) :
    HasNonnegativeDistributionalLevi
      (regularDistribution μ u (hu.continuous.locallyIntegrable.locallyIntegrableOn Ω)) := by
  intro v φ hφ
  rw [distributionalLeviCLM_regularDistribution hu v, regularDistribution_apply]
  apply integral_nonneg
  intro x
  by_cases hx : x ∈ Ω
  · exact mul_nonneg (hφ x) (hL x hx v)
  · have hφx : φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
    simp [hφx]

end Haar

end PshLines
