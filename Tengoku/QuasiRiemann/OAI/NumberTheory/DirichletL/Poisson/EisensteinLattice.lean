import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

def inverseJacobian (A : ℂ ≃L[ℝ] ℂ) : ℝ :=
  |(LinearMap.det (A : ℂ →ₗ[ℝ] ℂ))⁻¹|

/--
@isnad1 id=eq.0h2v.s9.41cc891c6f76 from=translated src=- shape=da5408b8 vocab=539c9014
-/
theorem integral_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (A x)) = inverseJacobian A • ∫ x : ℂ, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure ℂ))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure ℂ) =
      ENNReal.ofReal (inverseJacobian A) • volume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : ℂ, f y ∂Measure.map A volume) = (∫ x : ℂ, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (show 0 ≤ inverseJacobian A from abs_nonneg _)] at h
  exact h.symm

def dualMap (A : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ :=
  A.symm.toContinuousLinearMap.adjoint

/--
@isnad1 id=eq.0h3v.s9.41225f2837ea from=translated src=- shape=90320ef9 vocab=f81a6bce
-/
theorem inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

/--
@isnad1 id=eq.0h3v.s9.5883e16be827 from=translated src=- shape=6f543959 vocab=7d4ffff5
-/
theorem fourier_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl

def translateSchwartz (f : 𝓢(ℂ, ℂ)) (b : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : ℂ => z + b)
    (by fun_prop) (isometry_add_right b).antilipschitzWith f

/--
@isnad1 id=eq.0h3v.s7.da31f3b43156 from=translated src=- shape=0d977d19 vocab=aff583ab
-/
@[simp] theorem translateSchwartz_apply (f : 𝓢(ℂ, ℂ)) (b z : ℂ) :
    translateSchwartz f b z = f (z + b) := rfl

/--
@isnad1 id=eq.0h3v.s7.b9e6009f6002 from=translated src=- shape=06c4ae8d vocab=17293cd4
-/
theorem fourier_translate (f : ℂ → ℂ) (b w : ℂ) :
    𝓕 (fun z => f (z + b)) w =
      Real.fourierChar (inner ℝ b w) • 𝓕 f w := by
  exact congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℂ) (innerₗ ℂ) f b) w

def affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (translateSchwartz f b)

/--
@isnad1 id=eq.0h4v.s9.cff4a4c1701f from=translated src=- shape=e084132d vocab=19d4f4ea
-/
@[simp] theorem affinePullback_apply (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b z : ℂ) :
    affinePullback f A b z = f (A z + b) := rfl

/--
@isnad1 id=eq.0h4v.s9.d825a61b34d4 from=translated src=- shape=8dd13a27 vocab=3466a4b1
-/
theorem fourier_affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b w : ℂ) :
    (𝓕 (affinePullback f A b)) w =
      inverseJacobian A •
        (Real.fourierChar (inner ℝ b (dualMap A w)) • (𝓕 f) (dualMap A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => f (z + b)) ∘ A) w = _
  rw [fourier_comp_linearEquiv, fourier_translate]
  rw [congrFun (SchwartzMap.fourier_coe f) (dualMap A w)]

/--
@isnad1 id=eq.0h3v.s10.1cad30929e76 from=translated src=- shape=8e54efcc vocab=fa75e1a6
-/
theorem affine_lattice_poisson (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    (∑' p : ℤ × ℤ, f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + b)) =
      inverseJacobian A • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ b (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
          (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  have h := integer_pair_poisson (affinePullback f A b)
  simp only [affinePullback_apply, fourier_affinePullback] at h
  rw [tsum_const_smul''] at h
  exact h

end

section
open scoped RealInnerProductSpace

def basisMap (w : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM +
    w • (Complex.ofRealCLM.comp Complex.imCLM)

/--
@isnad1 id=eq.0h2v.s7.23eaf609c0b9 from=translated src=- shape=f2bc418c vocab=a9647059
-/
@[simp] theorem basisMap_apply (w z : ℂ) :
    basisMap w z = (z.re : ℂ) + w * (z.im : ℂ) := rfl

def basisEquiv (w : ℂ) (hw : w.im ≠ 0) : ℂ ≃L[ℝ] ℂ where
  toLinearEquiv :=
    { toLinearMap := (basisMap w).toLinearMap
      invFun z := complexPoint (z.re - z.im * w.re / w.im) (z.im / w.im)
      left_inv z := by
        change complexPoint ((basisMap w z).re - (basisMap w z).im * w.re / w.im)
          ((basisMap w z).im / w.im) = z
        apply Complex.ext
        · simp only [basisMap_apply, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
            Complex.add_im, Complex.mul_im,  zero_add, complexPoint]
          field_simp [hw]
          ring
        · simp [basisMap_apply, complexPoint, hw]
      right_inv z := by
        change basisMap w (complexPoint (z.re - z.im * w.re / w.im)
          (z.im / w.im)) = z
        apply Complex.ext
        · simp only [basisMap_apply, complexPoint, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
          field_simp [hw]
          ring
        · simp only [basisMap_apply, complexPoint, Complex.add_im,
            Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_add]
          field_simp [hw] }
  continuous_toFun := (basisMap w).continuous
  continuous_invFun := by
    simp only [complexPoint_eq]
    fun_prop

/--
@isnad1 id=eq.1h2v.s8.1bfb7f9622c4 from=translated src=- shape=9d1479ad vocab=626f13af
-/
@[simp] theorem basisEquiv_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    basisEquiv w hw z = (z.re : ℂ) + w * (z.im : ℂ) := rfl

/--
@isnad1 id=eq.1h2v.s8.d66db490575b from=translated src=- shape=fd94abba vocab=eeb88364
-/
@[simp] theorem basisEquiv_symm_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    (basisEquiv w hw).symm z =
      complexPoint (z.re - z.im * w.re / w.im) (z.im / w.im) := rfl

/--
@isnad1 id=eq.1h1v.s10.d82f910b39dc from=translated src=- shape=896b8eed vocab=b541e894
-/
theorem basisEquiv_det (w : ℂ) (hw : w.im ≠ 0) :
    LinearMap.det ((basisEquiv w hw) : ℂ →ₗ[ℝ] ℂ) = w.im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr, basisEquiv_apply]

def complexMulEquiv (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 c hc)

/--
@isnad1 id=eq.1h2v.s8.4dca3424795f from=translated src=- shape=0ed6251c vocab=b5b75bf4
-/
@[simp] theorem complexMulEquiv_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    complexMulEquiv c hc z = c * z := rfl

/--
@isnad1 id=eq.1h2v.s8.577559a791e4 from=translated src=- shape=55f7cb05 vocab=3fa53cff
-/
@[simp] theorem complexMulEquiv_symm_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (complexMulEquiv c hc).symm z = c⁻¹ * z := rfl

/--
@isnad1 id=eq.1h1v.s10.81594e80f11f from=translated src=- shape=b2047f46 vocab=ea56c1fe
-/
theorem complexMulEquiv_det (c : ℂ) (hc : c ≠ 0) :
    LinearMap.det ((complexMulEquiv c hc) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq c := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr, complexMulEquiv_apply, Complex.normSq_apply]

def scaledBasisEquiv (w : ℂ) (hw : w.im ≠ 0) (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  (basisEquiv w hw).trans (complexMulEquiv c hc)

/--
@isnad1 id=eq.2h3v.s8.8f610c571a17 from=translated src=- shape=2517dd76 vocab=aa38d02e
-/
@[simp] theorem scaledBasisEquiv_apply (w : ℂ) (hw : w.im ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    scaledBasisEquiv w hw c hc z = c * ((z.re : ℂ) + w * (z.im : ℂ)) := rfl

/--
@isnad1 id=eq.2h2v.s10.36d2e77101ab from=translated src=- shape=b102f710 vocab=8bc9717e
-/
theorem scaledBasisEquiv_det (w : ℂ) (hw : w.im ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    LinearMap.det ((scaledBasisEquiv w hw c hc) : ℂ →ₗ[ℝ] ℂ) =
      Complex.normSq c * w.im := by
  change LinearMap.det
    (((complexMulEquiv c hc) : ℂ →ₗ[ℝ] ℂ).comp ((basisEquiv w hw) : ℂ →ₗ[ℝ] ℂ)) = _
  rw [LinearMap.det_comp, complexMulEquiv_det, basisEquiv_det]

end

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace
abbrev O := ActualEisensteinCubic.O

def eisensteinLatticeMap (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  scaledBasisEquiv omega3 omega3_im_ne_zero c hc

/--
@isnad1 id=eq.1h2v.s8.30d42a8154ee from=translated src=- shape=4b6a5097 vocab=4e16bc9c
-/
theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

/--
@isnad1 id=eq.1h1v.s6.387cf4c2a701 from=translated src=- shape=59bb5ff8 vocab=854a7594
-/
theorem eisenstein_inverseJacobian (c : ℂ) (hc : c ≠ 0) :
    inverseJacobian (eisensteinLatticeMap c hc) = 2 / (Real.sqrt 3 * ‖c‖ ^ 2) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hn : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  unfold inverseJacobian eisensteinLatticeMap
  rw [scaledBasisEquiv_det, omega3_im, Complex.normSq_eq_norm_sq]
  rw [abs_of_pos (inv_pos.mpr (mul_pos hn (div_pos hs (by norm_num))))]
  field_simp

def eisensteinDualFrequency (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) : ℂ :=
  dualMap (eisensteinLatticeMap c hc) (complexPoint (p.1 : ℝ) (p.2 : ℝ))

/--
@isnad1 id=eq.1h3v.s9.c0e29f076940 from=translated src=- shape=cf2988f4 vocab=3986657c
-/
theorem actual_eisenstein_coset_poisson (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    (∑' z : O, f (eisEmbedding (b + c * z))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ (eisEmbedding b)
          (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := affine_lattice_poisson f A (eisEmbedding b)
  rw [eisenstein_inverseJacobian] at h
  calc
    (∑' z : O, f (eisEmbedding (b + c * z))) =
        ∑' p : ℤ × ℤ, f (eisEmbedding (b + c * latticeCoordEquiv.symm p)) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ,
        f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + eisEmbedding b) := by
      apply tsum_congr
      intro p
      congr 1
      rw [map_add, map_mul]
      change eisEmbedding b + eisEmbedding c *
          eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
      rw [← eisensteinLatticeMap_point]
      exact add_comm _ _
    _ = _ := h

/--
@isnad1 id=summable.1h3v.s7.14b1cac33383 from=translated src=- shape=c838435e vocab=df6e1db9
-/
theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

/--
@isnad1 id=summable.0h1v.s7.4f4c80e3d5eb from=translated src=- shape=763634f5 vocab=7d632d94
-/
theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

/--
@isnad1 id=summable.0h4v.s7.25c37ab84f86 from=translated src=- shape=357bf5d4 vocab=fa383edd
-/
theorem actual_eisenstein_periodic_summable (f : 𝓢(ℂ, ℂ))
    {R : Type*} [Fintype R] (q : O → R) (P : R → ℂ) :
    Summable (fun z : O => P (q z) * f (eisEmbedding z)) := by
  classical
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun a _ => norm_nonneg (P a)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((actual_eisenstein_summable_norm f).mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP (q z)) (norm_nonneg _)

/--
@isnad1 id=eq.1h3v.s10.75507cae8d67 from=translated src=- shape=606d21b4 vocab=ab85a55e
-/
theorem actual_eisenstein_periodic_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      ∑ r : O ⧸ Ideal.span {c}, P r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
          Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => f (eisEmbedding z))
    (actual_eisenstein_periodic_summable f _ P)]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (GaussianFiberEquiv.fiber_tsum c hc r
    (GaussianShiftedPartition.representative c r)
    (GaussianShiftedPartition.representative_spec c r)
    (fun z => f (eisEmbedding z))).trans
      (actual_eisenstein_coset_poisson f _ c hc)

/--
@isnad1 id=lt.0h1v.s6.3994ebac6308 from=translated src=- shape=1af84252 vocab=52bfc3d2
-/
theorem inverseJacobian_pos (A : ℂ ≃L[ℝ] ℂ) : 0 < inverseJacobian A :=
  abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)

/--
@isnad1 id=summable.0h2v.s9.7f4487da6871 from=translated src=- shape=0d6246b2 vocab=08c828b8
-/
theorem dual_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖) := by
  have hJ := inverseJacobian_pos A
  have hp := plane_lattice_summable_norm (𝓕 (affinePullback f A 0))
  have hn (p : ℤ × ℤ) :
      ‖(𝓕 (affinePullback f A 0)) (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖ =
      inverseJacobian A * ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖ := by
    rw [fourier_affinePullback]
    simp [ abs_of_pos hJ]
  simp_rw [hn] at hp
  have hi := hp.mul_left (inverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

/--
@isnad1 id=eq.0h5v.s10.b6977d7c9588 from=translated src=- shape=55cfd543 vocab=aebef1ba
-/
theorem finite_phase_sum {R : Type*} [Fintype R]
    (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : R → ℂ) (P : R → ℂ) :
    (∑ r : R, P r * (inverseJacobian A • ∑' p : ℤ × ℤ,
      Real.fourierChar (inner ℝ (b r) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) =
    inverseJacobian A • ∑' p : ℤ × ℤ,
      (∑ r : R, P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) : ℂ)) *
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  classical
  have hs (r : R) : Summable (fun p : ℤ × ℤ =>
      P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using dual_lattice_summable_norm f A
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [Circle.smul_def, smul_eq_mul, Finset.sum_mul, mul_assoc]

/--
@isnad1 id=eq.1h3v.s10.be6a793d9ef0 from=translated src=- shape=c9d06386 vocab=4c363487
-/
theorem actual_eisenstein_periodic_fourier (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)) *
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [actual_eisenstein_periodic_poisson f c hc P]
  have h := finite_phase_sum f
    (eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc))
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r)) P
  rw [eisenstein_inverseJacobian] at h
  exact h

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

/--
@isnad1 id=eq.0h3v.s10.8f985364ed1c from=translated src=- shape=5dec18b3 vocab=e48aac43
-/
theorem dualMap_trans (A B : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    dualMap (A.trans B) z = dualMap B (dualMap A z) := by
  change (ContinuousLinearMap.adjoint
    (A.symm.toContinuousLinearMap.comp B.symm.toContinuousLinearMap)) z = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

/--
@isnad1 id=eq.1h2v.s8.4085f97721ea from=translated src=- shape=1ddcf923 vocab=d7e711fd
-/
theorem dual_basis_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    dualMap (basisEquiv w hw) z =
      complexPoint z.re ((z.im - w.re * z.re) / w.im) := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((basisEquiv w hw).symm v) z = _
  simp only [basisEquiv_symm_apply, Complex.inner, complexPoint,
    Complex.mul_re,  Complex.conj_re, Complex.conj_im]
  field_simp [hw]
  ring

/--
@isnad1 id=eq.1h2v.s8.82647104b502 from=translated src=- shape=d4841452 vocab=9920dfb3
-/
theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

/--
@isnad1 id=eq.1h2v.s7.1a6b8d14c08c from=translated src=- shape=26b80963 vocab=e2eb0a48
-/
theorem eisensteinDualFrequency_explicit (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinDualFrequency c hc p =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
        starRingEnd ℂ c := by
  unfold eisensteinDualFrequency eisensteinLatticeMap scaledBasisEquiv
  rw [dualMap_trans, dual_basis_apply, dual_mul_apply]
  have he : complexPoint (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re
      (((complexPoint (p.1 : ℝ) (p.2 : ℝ)).im - omega3.re *
        (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re) / omega3.im) =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) := by
    apply Complex.ext
    · rfl
    · simp only [complexPoint, omega3_im]
      have hr : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]
      rw [hr]
      ring
  rw [he]
  ring

def explicitDualFrequency (c : ℂ) (p : ℤ × ℤ) : ℂ :=
  complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
    starRingEnd ℂ c

/--
@isnad1 id=eq.1h3v.s10.20e5cc7b7437 from=translated src=- shape=d1a26095 vocab=e80b257a
-/
theorem actual_eisenstein_poisson_explicit (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (explicitDualFrequency (eisEmbedding c) p)) : ℂ)) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
  simpa only [eisensteinDualFrequency_explicit, explicitDualFrequency] using
    actual_eisenstein_periodic_fourier f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

def radialTest (W : 𝓢(ℝ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℂ (Function.hasTemperateGrowth_norm_sq ℂ)
    ⟨1, 1, fun z => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      nlinarith [sq_nonneg (‖z‖ - 1)]⟩ W

/--
@isnad1 id=eq.0h2v.s7.a15880c6aef6 from=translated src=- shape=37e3c1b6 vocab=4ac178c9
-/
@[simp] theorem radialTest_apply (W : 𝓢(ℝ, ℂ)) (z : ℂ) :
    radialTest W z = W (‖z‖ ^ 2) := rfl

def compactRadialTest (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) : 𝓢(ℂ, ℂ) :=
  radialTest (hWc.toSchwartzMap hWs)

/--
@isnad1 id=eq.2h2v.s7.94096d4a6661 from=translated src=- shape=9b95be58 vocab=09f12704
-/
@[simp] theorem compactRadialTest_apply (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (z : ℂ) :
    compactRadialTest W hWc hWs z = W (‖z‖ ^ 2) := rfl

/--
@isnad1 id=eq.3h3v.s10.107a7288d43c from=translated src=- shape=fe14ced1 vocab=5a6ee49c
-/
theorem actual_radial_poisson (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (explicitDualFrequency (eisEmbedding c) p)) : ℂ)) *
          (𝓕 (compactRadialTest W hWc hWs)) (explicitDualFrequency (eisEmbedding c) p) := by
  simpa only [compactRadialTest_apply] using
    actual_eisenstein_poisson_explicit (compactRadialTest W hWc hWs) c hc P

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

namespace IdealGaussCRT

noncomputable def coordinateAddChar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) (i : ι) : AddChar (R i) ℂ := by
  classical
  exact {
    toFun := fun z => ψ (e.symm (Pi.single i z))
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro z w
      rw [Pi.single_add, map_add, AddChar.map_add_eq_mul] }

private theorem addChar_finite_sum {ι T : Type*} [AddCommMonoid T]
    (ψ : AddChar T ℂ) (s : Finset ι) (f : ι → T) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

/--
@isnad1 id=eq.0h6v.s8.9373154e06b9 from=translated src=- shape=02cd4ee6 vocab=82d8dacd
-/
theorem addChar_finite_crt_factor {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) (x : T) :
    ψ x = ∏ i, coordinateAddChar R e ψ i (e x i) := by
  classical
  have hx : (∑ i, e.symm (Pi.single i (e x i))) = x := by
    rw [← map_sum, Finset.univ_sum_single, e.symm_apply_apply]
  calc
    ψ x = ψ (∑ i, e.symm (Pi.single i (e x i))) := congrArg ψ hx.symm
    _ = ∏ i, ψ (e.symm (Pi.single i (e x i))) := addChar_finite_sum ψ _ _
    _ = _ := rfl

/--
@isnad1 id=eq.1h7v.s10.14be4d210845 from=translated src=- shape=8b08d32a vocab=d01a9bb0
-/
theorem gauss_transform_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      ∏ i, if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
  classical
  calc
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
        ∑ x : T, ∏ i, χ i (e x i) *
          coordinateAddChar R e ψ i (e h i * e x i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ (h * x)]
      simp only [map_mul, Pi.mul_apply, Finset.prod_mul_distrib]
    _ = ∑ x : ∀ i, R i, ∏ i, χ i (x i) *
          coordinateAddChar R e ψ i (e h i * x i) :=
      Equiv.sum_comp e.toEquiv (fun z : ∀ i, R i =>
        ∏ i, χ i (z i) * coordinateAddChar R e ψ i (e h i * z i))
    _ = _ := ShortDraftFiniteGaussFourier.product_gauss_transform
      R χ (coordinateAddChar R e ψ) hχ (e h)

/--
@isnad1 id=eq.1h7v.s10.db90b6c99ec8 from=translated src=- shape=2c4d7330 vocab=e48d585e
-/
theorem gauss_transform_finite_crt_scalar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      (∏ i, χ i (e h i))⁻¹ *
        ∑ x : T, (∏ i, χ i (e x i)) * ψ x := by
  classical
  have hbase := gauss_transform_finite_crt R e χ ψ hχ (1 : T)
  simp only [one_mul, map_one, Pi.one_apply, one_ne_zero, ↓reduceIte,
    inv_one, one_mul] at hbase
  rw [gauss_transform_finite_crt R e χ ψ hχ h, hbase]
  have hlocal (i : ι) :
      (if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i)) =
      (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
    split_ifs with hi
    · simp [hi]
    · rfl
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

/--
@isnad1 id=eq.1h3v.s7.ba54386e1e25 from=translated src=- shape=fe73a844 vocab=5de4f047
-/
theorem finite_prod_eq_iInf {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P)) :
    (∏ i, P i) = ⨅ i, P i := by
  simpa using (Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := P) (by
      intro i _ j _ hij
      exact hc hij))

noncomputable def quotientProdEquivPi {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P)) :
    (A ⧸ ∏ i, P i) ≃+* ∀ i, A ⧸ P i :=
  (Ideal.quotEquivOfEq (finite_prod_eq_iInf P hc)).trans
    (Ideal.quotientInfRingEquivPiQuotient P hc)

/--
@isnad1 id=eq.1h5v.s11.5bf0734cda70 from=translated src=- shape=8d75543b vocab=255a9f97
-/
@[simp] theorem quotientProdEquivPi_mk {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P))
    (a : A) (i : ι) :
    quotientProdEquivPi P hc (Ideal.Quotient.mk (∏ j, P j) a) i =
      Ideal.Quotient.mk (P i) a := by
  simp only [quotientProdEquivPi, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

/--
@isnad1 id=eq.2h6v.s13.4681f23e39ba from=translated src=- shape=93da9106 vocab=369d6dc5
-/
theorem gauss_transform_finite_ideal_crt {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, (P i).IsMaximal]
    [Fintype (A ⧸ ∏ i, P i)] [∀ i, Fintype (A ⧸ P i)]
    (χ : ∀ i, MulChar (A ⧸ P i) ℂ)
    (ψ : AddChar (A ⧸ ∏ i, P i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (h : A ⧸ ∏ i, P i) :
    (∑ x : A ⧸ ∏ i, P i, (∏ i, χ i (quotientProdEquivPi P hc x i)) * ψ (h * x)) =
      ∏ i, if quotientProdEquivPi P hc h i = 0 then 0 else
        (χ i (quotientProdEquivPi P hc h i))⁻¹ *
          gaussSum (χ i) (coordinateAddChar (fun i => A ⧸ P i)
            (quotientProdEquivPi P hc) ψ i) := by
  let (i : ι) : Field (A ⧸ P i) := Ideal.Quotient.field (P i)
  exact gauss_transform_finite_crt (fun i => A ⧸ P i)
    (quotientProdEquivPi P hc) χ ψ hχ h

end IdealGaussCRT

end

end OAI
