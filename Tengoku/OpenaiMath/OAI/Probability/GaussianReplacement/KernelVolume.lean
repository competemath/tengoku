import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.KernelGeometry

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

section KernelVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

abbrev KernelHistory (r n : ℕ) (E : Type*) := Fin n → ((Fin r → E) × E)

def kernelInverseVolume {r n : ℕ} (h : KernelHistory r n E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (‖gramSchmidt ℝ (fun j => (h j).2) i‖⁻¹)

omit measurableSpaceE borelSpaceE nontrivialE in
lemma kernelInverseVolume_snoc {r n : ℕ} (h : KernelHistory r n E)
    (z : (Fin r → E) × E) :
    kernelInverseVolume (Fin.snoc h z) = kernelInverseVolume h *
      ENNReal.ofReal ((Metric.infDist z.2 (rowSpan (fun j => (h j).2) : Set E))⁻¹) := by
  unfold kernelInverseVolume
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    congr 3
    rw [gramSchmidt_castSucc]
    simp only [Fin.snoc_castSucc]
  · congr 2
    rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, rowSpan]

def kernelHistoryLaw {r : ℕ}
    (ν : (n : ℕ) → Kernel (KernelHistory r n E) ((Fin r → E) × E)) :
    (n : ℕ) → Measure (KernelHistory r n E)
  | 0 => Measure.dirac (fun i => Fin.elim0 i)
  | n+1 => ((kernelHistoryLaw ν n) ⊗ₘ ν n).map (fun z => Fin.snoc z.1 z.2)

end KernelVolume

section KernelPiVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

omit finiteDimensionalRealE measurableSpaceE borelSpaceE nontrivialE in
lemma span_image_diagonal_smul {ι : Type*} (v : ι → E) (c : ι → ℝ)
    (hc : ∀ i, c i ≠ 0) (I : Set ι) :
    Submodule.span ℝ ((fun i => c i • v i) '' I) = Submodule.span ℝ (v '' I) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have h := Submodule.smul_mem (Submodule.span ℝ ((fun i => c i • v i) '' I))
      (c i)⁻¹ (Submodule.subset_span ⟨i, hi, rfl⟩)
    rw [inv_smul_smul₀ (hc i)] at h
    exact h

omit measurableSpaceE borelSpaceE nontrivialE in
lemma gramSchmidt_diagonal_smul {n : ℕ} (v : Fin n → E) (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (j : Fin n) :
    gramSchmidt ℝ (fun i => c i • v i) j = c j • gramSchmidt ℝ v j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    span_image_diagonal_smul v c hc, map_smul, smul_sub]

omit measurableSpaceE borelSpaceE nontrivialE in
lemma kernelInverseVolume_normalization {r n : ℕ}
    (h : KernelHistory r n E) (hn : ∀ i, (h i).2 ≠ 0) :
    kernelInverseVolume h =
      (∏ i, ENNReal.ofReal (‖(h i).2‖⁻¹)) *
        kernelInverseVolume (fun i => ((h i).1, ‖(h i).2‖⁻¹ • (h i).2)) := by
  unfold kernelInverseVolume
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [gramSchmidt_diagonal_smul _ _ (fun j => inv_ne_zero (norm_ne_zero_iff.mpr (hn j))),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_inv,
    inv_inv, ←mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hn i)), one_mul]

end KernelPiVolume

section KernelNormalizedMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

def normalizeKernelVector {r : ℕ} (z : (Fin r → E) × E) : (Fin r → E) × E :=
  (z.1, ‖z.2‖⁻¹ • z.2)

omit nontrivialE in
lemma measurable_normalizeKernelVector (r : ℕ) :
    Measurable (normalizeKernelVector (E:=E) (r:=r)) := by
  unfold normalizeKernelVector
  fun_prop

omit finiteDimensionalRealE measurableSpaceE borelSpaceE nontrivialE in
lemma normalizeKernelVector_support {r : ℕ} (z : (Fin r → E) × E)
    (hz : z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    ‖(normalizeKernelVector z).2‖ = 1 ∧
      (normalizeKernelVector z).2 ∈ (rowSpan (normalizeKernelVector z).1)ᗮ := by
  constructor
  · simp [normalizeKernelVector, norm_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz.1)]
  · exact Submodule.smul_mem _ _ hz.2

end KernelNormalizedMoment

end CurrentProjection

end

end OAI
