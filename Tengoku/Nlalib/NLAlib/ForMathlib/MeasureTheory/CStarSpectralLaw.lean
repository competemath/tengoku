import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.FaithfulSpectralSupport
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.SupportMap
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.CompactMomentUniqueness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual positive spectral laws and faithful moment transport

The genuine continuous-functional-calculus spectrum measure is pushed onto
the real line. Its moments, finite mass and actual compact support follow
from the construction. Faithfulness on a closed containing star algebra
identifies its support with the full operator spectrum. Equality of genuine
power moments then gives equality of the actual spectra and self-adjoint
operator norms, including trivial algebras and empty spectra.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology ComplexOrder ContinuousFunctionalCalculus
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem spectralLawRealCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus
attribute [local instance] spectralLawRealCFC

/-- The actual real-line spectral law of a positive functional and a self-adjoint element.-/
def positiveRealSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A} (ha : IsSelfAdjoint a) : Measure ℝ :=
  (positiveSpectrumMeasure φ ha).map Subtype.val

/--
@isnad1 id=isfinite.1h3v.s6.3a2b5ae34230 from=translated src=- shape=0fdcfa52 vocab=ff564e7a
-/
instance isFiniteMeasure_positiveRealSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) : IsFiniteMeasure (positiveRealSpectrumMeasure φ ha) :=
  inferInstanceAs (IsFiniteMeasure ((positiveSpectrumMeasure φ ha).map Subtype.val))

/-- Every continuous real test function integrates to the actual positive-functional continuous-functional-calculus value.
@isnad1 id=eq.2h4v.s8.535b3b3e9bb3 from=translated src=- shape=71c35748 vocab=3e7ee399
-/
theorem integral_positiveRealSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ x, f x ∂positiveRealSpectrumMeasure φ ha=(φ (cfc f a)).re := by
  rw [positiveRealSpectrumMeasure,integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]
  exact integral_comp_subtype_positiveSpectrumMeasure φ ha f hf.continuousOn

/-- The real-line spectral law has exactly the genuine operator power moments.
@isnad1 id=eq.1h4v.s7.f1d78e5709d5 from=translated src=- shape=849d92bb vocab=13bc89fb
-/
theorem integral_pow_positiveRealSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) (n : ℕ) :
    ∫ x, x^n ∂positiveRealSpectrumMeasure φ ha=(φ (a^n)).re := by
  rw [integral_positiveRealSpectrumMeasure φ ha _ (by fun_prop),cfc_pow_id a n ha]

/-- The actual real-line spectral law has mass equal to the functional value at one.
@isnad1 id=eq.1h3v.s7.0719e93eb625 from=translated src=- shape=3cfae893 vocab=5b21f11c
-/
theorem measureReal_univ_positiveRealSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) :
    (positiveRealSpectrumMeasure φ ha).real Set.univ=(φ 1).re := by
  simpa only [pow_zero,integral_const,smul_eq_mul,mul_one] using
    integral_pow_positiveRealSpectrumMeasure φ ha 0

/-- An actual normalized positive functional gives an actual spectral probability law.
@isnad1 id=isprobab.2h3v.s7.0fa9dde108c6 from=translated src=- shape=0f47178c vocab=8c869b69
-/
theorem isProbabilityMeasure_positiveRealSpectrumMeasure
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1) {a : A} (ha : IsSelfAdjoint a) :
    IsProbabilityMeasure (positiveRealSpectrumMeasure φ ha) := by
  rw [isProbabilityMeasure_iff_real,measureReal_univ_positiveRealSpectrumMeasure,hφ,Complex.one_re]

/-- The actual real-line law is supported on the native compact real spectrum.
@isnad1 id=eventual.1h3v.s7.2486d4092b9c from=translated src=- shape=fa9cd07f vocab=6d149c14
-/
theorem ae_mem_spectrum_positiveRealSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) :
    ∀ᵐ x ∂positiveRealSpectrumMeasure φ ha, x∈spectrum ℝ a := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) a).isClosed.measurableSet).mpr
  exact Filter.Eventually.of_forall fun x => x.property

/-- Faithfulness on a closed containing star algebra makes the actual real-line law support equal the entire native operator spectrum.
@isnad1 id=eq.4h4v.s9.05ad60c221fb from=translated src=- shape=379c6dd6 vocab=3af95e6f
-/
theorem support_positiveRealSpectrumMeasure_eq_spectrum
    (φ : A →ₚ[ℂ] ℂ) (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (hfaithful : ∀ b : A, b∈S → φ (star b*b)=0 → b=0)
    {a : A} (ha : IsSelfAdjoint a) (haS : a∈S) :
    (positiveRealSpectrumMeasure φ ha).support=spectrum ℝ a := by
  have hfull := support_positiveSpectrumMeasure_eq_univ_of_faithful φ S hS hfaithful ha haS
  have hh := Measure.support_map_eq_range_of_compact (positiveSpectrumMeasure φ ha)
    (Subtype.val : spectrum ℝ a → ℝ) continuous_subtype_val hfull
  simpa only [positiveRealSpectrumMeasure,Subtype.range_coe_subtype,Set.ofPred_mem_eq] using hh

section MomentUniqueness
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Matching genuine operator power moments identify the actual compactly supported real spectral laws.
@isnad1 id=eq.3h6v.s8.4c419107f91a from=translated src=- shape=0c2bdb49 vocab=0d4fb846
-/
theorem positiveRealSpectrumMeasure_eq_of_power_moments
    (φ : A →ₚ[ℂ] ℂ) (ψ : B →ₚ[ℂ] ℂ) {a : A} {b : B}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hmom : ∀ n : ℕ, (φ (a^n)).re=(ψ (b^n)).re) :
    positiveRealSpectrumMeasure φ ha=positiveRealSpectrumMeasure ψ hb := by
  let K := spectrum ℝ a ∪ spectrum ℝ b
  have hK : IsCompact K :=
    (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) a).union
      (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) b)
  apply Measure.eq_of_integral_pow_eq_of_ae_mem_isCompact hK
  · exact (ae_mem_spectrum_positiveRealSpectrumMeasure φ ha).mono fun x hx => Or.inl hx
  · exact (ae_mem_spectrum_positiveRealSpectrumMeasure ψ hb).mono fun x hx => Or.inr hx
  · intro n
    rw [integral_pow_positiveRealSpectrumMeasure,integral_pow_positiveRealSpectrumMeasure,hmom n]

/-- Matching genuine power moments and faithfulness on closed containing star algebras identify the full actual real spectra.
@isnad1 id=eq.9h8v.s10.6d7c852ce250 from=translated src=- shape=51695f2d vocab=a008e2b2
-/
theorem spectrum_real_eq_of_faithful_power_moments
    (φ : A →ₚ[ℂ] ℂ) (ψ : B →ₚ[ℂ] ℂ)
    (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (T : StarSubalgebra ℂ B) (hT : IsClosed (T : Set B))
    (hfaithfulA : ∀ c : A, c∈S → φ (star c*c)=0 → c=0)
    (hfaithfulB : ∀ c : B, c∈T → ψ (star c*c)=0 → c=0)
    {a : A} {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (haS : a∈S) (hbT : b∈T)
    (hmom : ∀ n : ℕ, (φ (a^n)).re=(ψ (b^n)).re) : spectrum ℝ a=spectrum ℝ b := by
  have heq := positiveRealSpectrumMeasure_eq_of_power_moments φ ψ ha hb hmom
  calc
    spectrum ℝ a=(positiveRealSpectrumMeasure φ ha).support :=
      (support_positiveRealSpectrumMeasure_eq_spectrum φ S hS hfaithfulA ha haS).symm
    _=(positiveRealSpectrumMeasure ψ hb).support := congrArg Measure.support heq
    _=spectrum ℝ b := support_positiveRealSpectrumMeasure_eq_spectrum ψ T hT hfaithfulB hb hbT

/-- Matching genuine power moments under faithful positive functionals identify the actual self-adjoint operator norms.
@isnad1 id=eq.9h8v.s10.127b20ec6a2e from=translated src=- shape=3ba0d309 vocab=966d6374
-/
theorem norm_eq_of_faithful_power_moments
    (φ : A →ₚ[ℂ] ℂ) (ψ : B →ₚ[ℂ] ℂ)
    (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (T : StarSubalgebra ℂ B) (hT : IsClosed (T : Set B))
    (hfaithfulA : ∀ c : A, c∈S → φ (star c*c)=0 → c=0)
    (hfaithfulB : ∀ c : B, c∈T → ψ (star c*c)=0 → c=0)
    {a : A} {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (haS : a∈S) (hbT : b∈T)
    (hmom : ∀ n : ℕ, (φ (a^n)).re=(ψ (b^n)).re) : ‖a‖=‖b‖ := by
  have hs := spectrum_real_eq_of_faithful_power_moments φ ψ S hS T hT
    hfaithfulA hfaithfulB ha hb haS hbT hmom
  rw [← ha.toReal_spectralRadius_eq_norm,← hb.toReal_spectralRadius_eq_norm]
  simp only [spectralRadius,hs]

end MomentUniqueness
