import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LocalInjectivePartition
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.MultiplicityIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Equal-dimensional C¹ maps have countable fibers outside a null target set.
The regular locus admits measurable injective pieces, and its Jacobian estimate
extends across the singular locus because the determinant is zero there. These
real measure-theoretic statements are used for integration only; they do not
replace the common-radius proof of asymptotic critical-value finiteness. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

theorem ae_countable_fibers_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    (S : Set E) (f : E → E) (D : E → E →L[ℝ] E)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x)
    (hD : ∀ x ∈ S, HasFDerivAt f (D x) x) :
    ∀ᵐ y ∂μ, ({x | x ∈ S ∧ f x = y}).Countable := by
  let C : Set E := {x | x ∈ S ∧ (D x).det = 0}
  let R : Set E := {x | x ∈ S ∧ (D x).det ≠ 0}
  have hnull : μ (f '' C) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hD x hx.1).hasFDerivWithinAt) (fun x hx => hx.2)
  have hloc : ∀ x ∈ R, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U := by
    intro x hx
    exact exists_open_injective_of_contDiffAt_det_ne_zero (hf x hx.1) (hD x hx.1) hx.2
  have hgood : ∀ᵐ y ∂μ, y ∉ f '' C := by
    exact measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hgood] with y hy
  have he : {x | x ∈ S ∧ f x = y} = {x | x ∈ R ∧ f x = y} := by
    ext x
    simp only [Set.mem_ofPred_eq, R]
    constructor
    · rintro ⟨hx, hxy⟩
      exact ⟨⟨hx, fun hz => hy ⟨x, ⟨hx, hz⟩, hxy⟩⟩, hxy⟩
    · rintro ⟨⟨hx, _⟩, hxy⟩
      exact ⟨hx, hxy⟩
  rw [he]
  exact countable_fiber_of_local_injectivity R f hloc y

theorem measurableSet_regular_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (S : Set E) (hS : MeasurableSet S) (f : E → E) (D : E → E →L[ℝ] E)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x)
    (hD : ∀ x ∈ S, HasFDerivAt f (D x) x) :
    MeasurableSet {x | x ∈ S ∧ (D x).det ≠ 0} := by
  have hc : ContinuousOn D S :=
    (show ContinuousOn (fderiv ℝ f) S from fun x hx =>
      ((hf x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt).congr
        (fun x hx => (hD x hx).fderiv.symm)
  have hd : ContinuousOn (fun x => (D x).det) S :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hc
  obtain ⟨U, hU, he⟩ := continuousOn_iff'.mp hd ({0}ᶜ) isClosed_singleton.isOpen_compl
  have hh : {x | x ∈ S ∧ (D x).det ≠ 0} = U ∩ S := by
    rw [← he]
    ext x
    simp [and_comm]
  rw [hh]
  exact hU.measurableSet.inter hS

/-- The Jacobian vanishes on the singular part; regular points admit a
countable measurable injective partition. No partition is supplied as input.-/
theorem lintegral_abs_det_le_mul_image_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    (S : Set E) (hS : MeasurableSet S) (f : E → E) (D : E → E →L[ℝ] E)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x)
    (hD : ∀ x ∈ S, HasFDerivAt f (D x) x) (N : ℕ)
    (hN : ∀ᵐ y ∂μ, ({x | x ∈ S ∧ f x = y}).Finite ∧
      ({x | x ∈ S ∧ f x = y}).ncard ≤ N) :
    (∫⁻ x in S, ENNReal.ofReal |(D x).det| ∂μ) ≤
      (N : ℝ≥0∞) * μ (f '' S) := by
  classical
  let R : Set E := {x | x ∈ S ∧ (D x).det ≠ 0}
  have hR : MeasurableSet R := measurableSet_regular_of_contDiffAt S hS f D hf hD
  have hRS : R ⊆ S := fun _ hx => hx.1
  obtain ⟨A, hA, hdisj, hcover, hinj⟩ := exists_measurable_injective_partition R hR f
    (fun x hx => exists_open_injective_of_contDiffAt_det_ne_zero
      (hf x hx.1) (hD x hx.1) hx.2)
  have hAS (i : ℕ) : A i ⊆ S := by
    have hh : A i ⊆ R := by rw [← hcover]; exact subset_iUnion A i
    exact hh.trans hRS
  have hb := lintegral_abs_det_le_mul_image_of_countable_pieces μ A hA hdisj f D
    (fun i x hx => (hD x (hAS i hx)).hasFDerivWithinAt) hinj N (by
      filter_upwards [hN] with y hy
      have hh := image_membership_count_le_fiber A hdisj S hAS f y hy.1
      exact ⟨hh.1, hh.2.trans hy.2⟩)
  rw [hcover] at hb
  have he : (∫⁻ x in S, ENNReal.ofReal |(D x).det| ∂μ) =
      ∫⁻ x in R, ENNReal.ofReal |(D x).det| ∂μ := by
    rw [← lintegral_indicator hS, ← lintegral_indicator hR]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ S
    · by_cases hd : (D x).det = 0
      · simp [Set.indicator_of_mem hx, R, hd]
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ R from ⟨hx, hd⟩)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hRS h))]
  rw [he]
  exact hb.trans (mul_le_mul_right (measure_mono (Set.image_mono hRS)) _)

end
end DuistermaatVanDerKallen
