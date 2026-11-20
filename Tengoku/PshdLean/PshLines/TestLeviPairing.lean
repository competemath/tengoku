import Tengoku.PshdLean.PshLines.SmoothDistribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Levi operators paired with actual test functions

For locally integrable densities, the distributional Levi operator pairs with
the classical Levi form of the test function. Its support is contained in the
test function's compact support, and its integral under a Haar measure is zero. A localized
deficit pairs with its negative, provided localization contains the support of
the test function. No regularity of the density beyond local integrability is
used in the pairing identity.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

namespace PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Opens E}

/-- The actual Hessian vanishes off the topological support of its function.
No differentiability hypothesis is needed for this support assertion.
@isnad1 id=eq.1h5v.s5.efb3f3269ef9 from=translated src=- shape=da3d181a vocab=f823c359
-/
theorem realHessian_eq_zero_of_notMem_tsupport {f : E → ℝ} {x : E}
    (hx : x ∉ tsupport f) (v w : E) : realHessian f x v w = 0 := by
  have hD : iteratedFDeriv ℝ 2 f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hxD =>
      hx (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) 2 hxD))
  simp only [realHessian, hD, zero_apply]

/--
@isnad1 id=le.0h4v.s5.219e314cd34b from=translated src=- shape=e6c19366 vocab=c5c11aa4
-/
theorem tsupport_realHessian_subset (f : E → ℝ) (v w : E) :
    tsupport (fun x => realHessian f x v w) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxf
  exact hx (realHessian_eq_zero_of_notMem_tsupport hxf v w)

/-- Two infinite-order bundled test-function derivatives agree with the
actual real Hessian, with outer direction first.
@isnad1 id=eq.0h6v.s10.b5fe9ad013d9 from=translated src=- shape=695e2935 vocab=d925dcac
-/
theorem testFunction_lineDerivCLM_lineDerivCLM_apply (φ : 𝓓(Ω, ℝ)) (x v w : E) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ) x =
      realHessian φ x v w := by
  have hinner :
      ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ) : E → ℝ) =
        fun y => fderiv ℝ φ y w :=
    funext (fun y => testFunction_lineDerivCLM_apply_eq_fderiv φ w y)
  rw [testFunction_lineDerivCLM_apply_eq_fderiv, hinner,
    fderiv_fderiv_apply_eq_realHessian
      (φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]

section RegularPairing

variable [MeasurableSpace E] [OpensMeasurableSpace E]
variable {μ : Measure E} {u : E → ℝ}

/-- Local integrability on the test-function domain suffices for integrability
of the density against each second derivative of a test function.
@isnad1 id=integrab.1h7v.s8.7aeeb6e1ae58 from=translated src=- shape=a2369603 vocab=4cdcd566
-/
theorem integrable_mul_realHessian_testFunction (hu : LocallyIntegrableOn u Ω μ)
    (φ : 𝓓(Ω, ℝ)) (v w : E) :
    Integrable (fun x => u x * realHessian φ x v w) μ := by
  have h := TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ))
  simpa only [testFunction_lineDerivCLM_lineDerivCLM_apply,
    ContinuousLinearMap.mul_apply', mul_comm] using h

variable [NormedSpace ℂ E]

/-- The density times the test function's classical Levi form is integrable.
@isnad1 id=integrab.1h6v.s8.f10bc64c5237 from=translated src=- shape=4438f07d vocab=0b4b3b58
-/
theorem integrable_mul_leviForm_testFunction (hu : LocallyIntegrableOn u Ω μ)
    (φ : 𝓓(Ω, ℝ)) (v : E) :
    Integrable (fun x => u x * leviForm φ x v) μ := by
  have h := ((integrable_mul_realHessian_testFunction hu φ v v).add
    (integrable_mul_realHessian_testFunction hu φ (Complex.I • v) (Complex.I • v))).div_const 4
  exact h.congr (Eventually.of_forall (fun x => by simp only [leviForm, Pi.add_apply]; ring))

/-- Pairing a distributional Levi derivative with a test function transfers
both derivatives to that test function, with two cancelling signs.
@isnad1 id=eq.1h6v.s11.0eb2ec99483b from=translated src=- shape=80989aa3 vocab=17c53cbd
-/
theorem distributionalLeviCLM_regularDistribution_apply
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    distributionalLeviCLM v (regularDistribution μ u hu) φ =
      ∫ x, u x * leviForm φ x v ∂μ := by
  have hA : Integrable (fun x => realHessian φ x v v * u x) μ := by
    simpa only [mul_comm] using integrable_mul_realHessian_testFunction hu φ v v
  have hB : Integrable
      (fun x => realHessian φ x (Complex.I • v) (Complex.I • v) * u x) μ := by
    simpa only [mul_comm] using
      integrable_mul_realHessian_testFunction hu φ (Complex.I • v) (Complex.I • v)
  rw [distributionalLeviCLM_apply, regularDistribution_apply, regularDistribution_apply]
  simp only [testFunction_lineDerivCLM_lineDerivCLM_apply]
  rw [← integral_add hA hB, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [leviForm]; ring)

end RegularPairing

section LeviSupport

variable [NormedSpace ℂ E]

/-- The classical Levi form vanishes outside the support of its function.
@isnad1 id=eq.1h4v.s6.33301e563091 from=translated src=- shape=ae34ddc7 vocab=8d8378da
-/
theorem leviForm_eq_zero_of_notMem_tsupport {f : E → ℝ} {x : E}
    (hx : x ∉ tsupport f) (v : E) : leviForm f x v = 0 := by
  rw [leviForm, realHessian_eq_zero_of_notMem_tsupport hx,
    realHessian_eq_zero_of_notMem_tsupport hx]
  norm_num

/--
@isnad1 id=le.0h3v.s6.73d9e4015231 from=translated src=- shape=596b3207 vocab=43face69
-/
theorem tsupport_leviForm_subset (f : E → ℝ) (v : E) :
    tsupport (fun x => leviForm f x v) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxf
  exact hx (leviForm_eq_zero_of_notMem_tsupport hxf v)

end LeviSupport

section Haar

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The integral of any second directional derivative of a test function is
zero. This follows from the proved integration-by-parts theorem for the
constant density; the constant density need not be globally integrable.
@isnad1 id=eq.0h6v.s7.4d40cc44cdd3 from=translated src=- shape=c1c9e8f3 vocab=bd752e11
-/
theorem integral_realHessian_testFunction (φ : 𝓓(Ω, ℝ)) (v w : E) :
    (∫ x, realHessian φ x v w ∂μ) = 0 := by
  have h := congrArg
    (fun T : 𝓓'(Ω, ℝ) =>
      T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ))
    (lineDerivCLM_regularDistribution (μ := μ)
      (show ContDiff ℝ 1 (fun _ : E => (1 : ℝ)) from contDiff_const) v)
  simp only [Distribution.lineDerivCLM_apply, regularDistribution_apply,
    testFunction_lineDerivCLM_lineDerivCLM_apply, fderiv_const_apply,
    zero_apply, mul_one, mul_zero, integral_zero] at h
  exact neg_eq_zero.mp h

variable [NormedSpace ℂ E]

/-- A test function's Levi form has integral zero.
@isnad1 id=eq.0h5v.s7.ecab180f3159 from=translated src=- shape=04bb7318 vocab=7fbca304
-/
theorem integral_leviForm_testFunction (φ : 𝓓(Ω, ℝ)) (v : E) :
    (∫ x, leviForm φ x v ∂μ) = 0 := by
  have hc : LocallyIntegrableOn (fun _ : E => (1 : ℝ)) Ω μ :=
    locallyIntegrableOn_const 1
  have hA : Integrable (fun x => realHessian φ x v v) μ := by
    simpa only [one_mul] using integrable_mul_realHessian_testFunction hc φ v v
  have hB : Integrable (fun x => realHessian φ x (Complex.I • v) (Complex.I • v)) μ := by
    simpa only [one_mul] using
      integrable_mul_realHessian_testFunction hc φ (Complex.I • v) (Complex.I • v)
  simp only [leviForm]
  rw [integral_div, integral_add hA hB, integral_realHessian_testFunction,
    integral_realHessian_testFunction]
  norm_num

/-- If the localization contains the test-function support, the localized
deficit pairs with the negative distributional Levi derivative of the original
density. No assumptions outside the test-function domain, and no measurability
of the localization set, are needed for this pairing identity.
@isnad1 id=eq.2h8v.s11.044bff9ce4a0 from=translated src=- shape=88888ac5 vocab=3e96491e
-/
theorem integral_indicator_deficit_mul_leviForm_testFunction {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) {K : Set E}
    (hφK : tsupport (φ : E → ℝ) ⊆ K) (C : ℝ) (v : E) :
    (∫ x, K.indicator (fun y => C - u y) x * leviForm φ x v ∂μ) =
      -distributionalLeviCLM v (regularDistribution μ u hu) φ := by
  classical
  have heq : (fun x => K.indicator (fun y => C - u y) x * leviForm φ x v) =
      fun x => C * leviForm φ x v - u x * leviForm φ x v := by
    funext x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      ring
    · have hzero : leviForm φ x v = 0 :=
        leviForm_eq_zero_of_notMem_tsupport (fun hxφ => hx (hφK hxφ)) v
      simp only [Set.indicator_of_notMem hx, hzero, mul_zero, sub_zero]
  have hconst : Integrable (fun x => C * leviForm φ x v) μ :=
    integrable_mul_leviForm_testFunction (locallyIntegrableOn_const C) φ v
  rw [heq, integral_sub hconst (integrable_mul_leviForm_testFunction hu φ v),
    integral_const_mul, integral_leviForm_testFunction, mul_zero, zero_sub,
    distributionalLeviCLM_regularDistribution_apply]

end Haar

end PshLines
