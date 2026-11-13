import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesUniqueness
import Tengoku.Seed.MeasureTheory.VectorMeasure.Integral
import Tengoku.Seed.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Signed Stieltjes transforms

The native vector-measure integral extends the scalar Cauchy kernel to
finite signed measures. Jordan decomposition and positive-measure
uniqueness then give signed uniqueness without support assumptions.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace MeasureTheory.SignedMeasure

/-- Signed measures have finite native variation.
@isnad1 id=isfinite.0h1v.s4.7e34434fc44f from=translated src=- shape=efd9f529 vocab=5b6fd474
-/
instance isFiniteMeasure_variation (s : SignedMeasure ℝ) : IsFiniteMeasure s.variation := by
  rw [← s.totalVariation_eq_variation]
  infer_instance

/-- Upper-half-plane Cauchy kernels are integrable for every signed real measure.
@isnad1 id=integrab.1h2v.s5.b207ea72d757 from=translated src=- shape=18f51a28 vocab=404b1055
-/
theorem integrable_real_cauchyKernel (s : SignedMeasure ℝ) {z : ℂ} (hz : 0 < z.im) :
    s.Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) :=
  Complex.integrable_real_cauchyKernel s.variation hz

/-- The native signed-measure Stieltjes transform, with kernel `(x-z)⁻¹`.-/
def stieltjesTransform (s : SignedMeasure ℝ) (z : ℂ) : ℂ :=
  ∫ᵛ x : ℝ, ((x : ℂ) - z)⁻¹ ∂<•s

/-- The transform of a positive measure's signed version is its usual integral.
@isnad1 id=eq.0h2v.s5.5e10a222a221 from=translated src=- shape=60741bd1 vocab=ed186398
-/
@[simp] theorem stieltjesTransform_toSignedMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ) :
    stieltjesTransform μ.toSignedMeasure z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ := by
  exact VectorMeasure.integral_toSignedMeasure

/-- Signed Stieltjes transforms preserve addition.
@isnad1 id=eq.1h3v.s6.0ec1e253875d from=translated src=- shape=581e6f60 vocab=9bffdc25
-/
theorem stieltjesTransform_add (s t : SignedMeasure ℝ) {z : ℂ} (hz : 0 < z.im) :
    stieltjesTransform (s + t) z = stieltjesTransform s z + stieltjesTransform t z := by
  exact VectorMeasure.integral_add_vectorMeasure
    (s.integrable_real_cauchyKernel hz) (t.integrable_real_cauchyKernel hz)

/-- Signed Stieltjes transforms preserve real scalar multiplication.
@isnad1 id=eq.0h3v.s6.91ad9865013b from=translated src=- shape=d4efcda6 vocab=b8c7ef6a
-/
@[simp] theorem stieltjesTransform_smul (a : ℝ) (s : SignedMeasure ℝ) (z : ℂ) :
    stieltjesTransform (a • s) z = a • stieltjesTransform s z := by
  exact VectorMeasure.integral_smul_vectorMeasure _ _

/-- Signed Stieltjes transforms preserve subtraction.
@isnad1 id=eq.1h3v.s6.a698e2550f77 from=translated src=- shape=581e6f60 vocab=0db242b2
-/
theorem stieltjesTransform_sub (s t : SignedMeasure ℝ) {z : ℂ} (hz : 0 < z.im) :
    stieltjesTransform (s - t) z = stieltjesTransform s z - stieltjesTransform t z := by
  exact VectorMeasure.integral_sub_vectorMeasure
    (s.integrable_real_cauchyKernel hz) (t.integrable_real_cauchyKernel hz)

/-- A signed measure is determined by its upper-half-plane Stieltjes transform.-/
theorem eq_zero_of_stieltjesTransform_eq_zero (s : SignedMeasure ℝ)
    (h : ∀ z : ℂ, 0 < z.im → stieltjesTransform s z = 0) : s = 0 := by
  let p := s.toJordanDecomposition.posPart
  let q := s.toJordanDecomposition.negPart
  have he : p.toSignedMeasure - q.toSignedMeasure = s :=
    s.toSignedMeasure_toJordanDecomposition
  have hpq : p = q := by
    apply measure_eq_of_integral_real_cauchyKernel_eq
    intro z hz
    have hs := h z hz
    rw [← he, stieltjesTransform_sub _ _ hz,
      stieltjesTransform_toSignedMeasure, stieltjesTransform_toSignedMeasure] at hs
    exact sub_eq_zero.mp hs
  exact he.symm.trans (sub_eq_zero.mpr (Measure.toSignedMeasure_congr hpq))

/-- Equal signed Stieltjes transforms imply equal signed measures.-/
theorem eq_of_stieltjesTransform_eq (s t : SignedMeasure ℝ)
    (h : ∀ z : ℂ, 0 < z.im → stieltjesTransform s z = stieltjesTransform t z) : s = t := by
  apply sub_eq_zero.mp
  apply eq_zero_of_stieltjesTransform_eq_zero
  intro z hz
  rw [stieltjesTransform_sub _ _ hz, h z hz, sub_self]

/-- Signed Stieltjes transforms commute with finite sums.
@isnad1 id=eq.1h4v.s5.00c6445ea291 from=translated src=- shape=ff696e69 vocab=1cd98b13
-/
theorem stieltjesTransform_sum {κ : Type*} (t : Finset κ) (s : κ → SignedMeasure ℝ)
    {z : ℂ} (hz : 0 < z.im) :
    stieltjesTransform (∑ k ∈ t, s k) z = ∑ k ∈ t, stieltjesTransform (s k) z := by
  exact VectorMeasure.integral_finsetSum_vectorMeasure
    (fun k _ => (s k).integrable_real_cauchyKernel hz)

/-- Signed Stieltjes transforms preserve negation.
@isnad1 id=eq.0h2v.s5.5a3d881042a6 from=translated src=- shape=b24c17e7 vocab=8f4989ad
-/
@[simp] theorem stieltjesTransform_neg (s : SignedMeasure ℝ) (z : ℂ) :
    stieltjesTransform (-s) z = -stieltjesTransform s z := by
  exact VectorMeasure.integral_neg_vectorMeasure

end MeasureTheory.SignedMeasure
