import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_integrable_mul_of_integral_subgroup_translate_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_integrable_mul_of_integral_subgroup_translate_eq_one.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_integrable_mul_of_integral_subgroup_translate_eq_one

set_option autoImplicit false

open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace P2mSectionIntegralB

section Setup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]

theorem measurable_subgroup_mul [SecondCountableTopology G] :
    Measurable fun p : G × T => ((p.2 : G) * p.1) := by
  have hc : Continuous fun p : G × T => ((p.2 : G) * p.1) :=
    (continuous_subtype_val.comp continuous_snd).mul continuous_fst
  exact hc.measurable

theorem measurable_fibre {w : G → ℝ} (hw : Measurable w) (x : G) :
    Measurable fun t : T => w ((t : G) * x) :=
  hw.comp ((continuous_subtype_val.mul continuous_const).measurable)

end Setup

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]
  (μ : Measure G) (τ : Measure T)

theorem lintegral_fibre_eq_one {w : G → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hw : Measurable w) {x : G}
    (h : ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => hw0 _)
    (measurable_fibre T hw x).aestronglyMeasurable] at h
  exact (ENNReal.toReal_eq_one_iff _).1 h

variable [μ.IsHaarMeasure] [τ.IsHaarMeasure] [τ.IsInvInvariant] (hT : IsClosed (T : Set G))
include hT

theorem sigmaCompactSpace_subgroup : SigmaCompactSpace T :=
  hT.isClosedEmbedding_subtypeVal.sigmaCompactSpace

theorem sFinite_tau : SFinite τ := by
  haveI := sigmaCompactSpace_subgroup T hT
  infer_instance

theorem lintegral_enorm_mul_lt_top (F : G → ℂ) (hFm : Measurable F) {C : ℝ} (hFb : ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w : G → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hw1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ < ∞ := by
  haveI := sFinite_tau T τ hT

  obtain ⟨U, hUo, hCU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hwc.isCompact
  obtain ⟨V₀, hV₀, hV₀U⟩ := compact_open_separated_mul_left hwc.isCompact hUo hCU
  obtain ⟨V, hVV₀, hVo, h1V⟩ := mem_nhds_iff.1 hV₀

  set m : ℝ≥0∞ := min (τ ((Subtype.val : T → G) ⁻¹' V)) 1 with hm
  have hm_pos : m ≠ 0 := by
    have h1 : (τ ((Subtype.val : T → G) ⁻¹' V)) ≠ 0 :=
      ((hVo.preimage continuous_subtype_val).measure_pos τ ⟨⟨1, T.one_mem⟩, h1V⟩).ne'
    simp [hm, h1]
  have hm_top : m ≠ ∞ := by simp [hm]
  have hm_le_one : m ≤ 1 := min_le_right _ _

  let Φ₀ : G → ℝ≥0∞ := fun x => ∫⁻ t : T, U.indicator 1 ((t : G) * x) ∂τ
  have hΦ₀ : ∀ x ∈ tsupport w, m ≤ Φ₀ x := by
    intro x hx
    have hsub : (Subtype.val : T → G) ⁻¹' V ⊆ (fun t : T => (t : G) * x) ⁻¹' U := by
      intro t ht
      exact hV₀U (Set.mul_mem_mul (hVV₀ ht) hx)
    calc m ≤ τ ((Subtype.val : T → G) ⁻¹' V) := min_le_left _ _
      _ ≤ τ ((fun t : T => (t : G) * x) ⁻¹' U) := measure_mono hsub
      _ = Φ₀ x := by
        have hUx : MeasurableSet ((fun t : T => (t : G) * x) ⁻¹' U) :=
          measurableSet_preimage ((continuous_subtype_val.mul continuous_const).measurable)
            hUo.measurableSet
        simp only [Φ₀]
        rw [← lintegral_indicator_one hUx]
        rfl

  have hUind : Measurable (U.indicator (1 : G → ℝ≥0∞)) :=
    (measurable_one.indicator hUo.measurableSet)
  have hint2 : Measurable fun p : G × T =>
      ‖F p.1‖ₑ * ENNReal.ofReal (w p.1) * U.indicator 1 ((p.2 : G) * p.1) :=
    ((hFm.comp measurable_fst).enorm.mul
      (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst))).mul
      (hUind.comp (measurable_subgroup_mul T))

  have step1 : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ ≤
      m⁻¹ * ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm_pos)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ tsupport w
    · have h1 : (1 : ℝ≥0∞) ≤ m⁻¹ * Φ₀ x := by
        calc (1 : ℝ≥0∞) = m⁻¹ * m := (ENNReal.inv_mul_cancel hm_pos hm_top).symm
          _ ≤ m⁻¹ * Φ₀ x := mul_le_mul_right (hΦ₀ x hx) _
      calc ‖F x‖ₑ * ENNReal.ofReal (w x) = ‖F x‖ₑ * ENNReal.ofReal (w x) * 1 := (mul_one _).symm
        _ ≤ ‖F x‖ₑ * ENNReal.ofReal (w x) * (m⁻¹ * Φ₀ x) := mul_le_mul_right h1 _
        _ = m⁻¹ * (‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x) := by ring
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp

  have step2 : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ =
      ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ := by
    calc ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ
        = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w x) * U.indicator 1 ((t : G) * x) ∂τ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * U.indicator 1 ((t : G) * x) ∂μ ∂τ :=
          lintegral_lintegral_swap hint2.aemeasurable
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G)⁻¹ * x)) * U.indicator 1 x ∂μ ∂τ := by
          refine lintegral_congr fun t => ?_
          have := lintegral_mul_left_eq_self (μ := μ)
            (fun x => ‖F ((t : G)⁻¹ * x)‖ₑ * ENNReal.ofReal (w ((t : G)⁻¹ * x)) * U.indicator 1 x) (t : G)
          simp only [inv_mul_cancel_left] at this
          rw [this]
          refine lintegral_congr fun x => ?_
          have hF : F ((t : G)⁻¹ * x) = F x := by
            have := hFT t⁻¹ x
            simpa using this
          rw [hF]
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G) * x)) * U.indicator 1 x ∂μ ∂τ := by
          rw [← lintegral_inv_eq_self]
          simp
      _ = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G) * x)) * U.indicator 1 x ∂τ ∂μ := by
          refine (lintegral_lintegral_swap ?_).symm
          exact (((hFm.comp measurable_fst).enorm.mul
            (ENNReal.measurable_ofReal.comp (hwm.comp (measurable_subgroup_mul T)))).mul
            (hUind.comp measurable_fst)).aemeasurable
      _ = ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_const_mul' _ _
            (ENNReal.mul_ne_top enorm_ne_top (by by_cases hxU : x ∈ U <;> simp [hxU]))]
          refine lintegral_congr fun t => ?_
          ring

  have step3 : ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ ≤
      ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ := by
    refine lintegral_mono fun x => ?_
    by_cases hF : F x = 0
    · simp [hF]
    · rw [lintegral_fibre_eq_one T τ hw0 hwm (hw1 x hF), mul_one]
      by_cases hxU : x ∈ U
      · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, Pi.one_apply, mul_one]
        have h : ‖F x‖₊ ≤ ‖C‖₊ := by
          rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
          exact (hFb x).trans (Real.le_norm_self C)
        exact enorm_le_coe.2 h
      · simp [hxU]
  have step4 : ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ < ∞ := by
    rw [lintegral_indicator_const hUo.measurableSet]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((measure_mono subset_closure).trans_lt hUc.measure_lt_top)
  calc ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ
      ≤ m⁻¹ * ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ := step1
    _ ≤ m⁻¹ * ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ := by
        rw [step2]; exact mul_le_mul_right step3 _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hm_pos)) step4

end Main

end P2mSectionIntegralB

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w : G → ℝ)
    (hw : (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    Integrable (fun x => F x * (w x : ℂ)) μ := by
  obtain ⟨C, hC⟩ := hFb
  obtain ⟨hw0, hwm, hwc, hw1⟩ := hw
  refine ⟨(hFm.mul (Complex.measurable_ofReal.comp hwm)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h : ∀ x, ‖F x * (w x : ℂ)‖ₑ = ‖F x‖ₑ * ENNReal.ofReal (w x) := by
    intro x
    rw [enorm_mul, ← ofReal_norm (w x : ℂ), Complex.norm_real, Real.norm_of_nonneg (hw0 x)]
  simp_rw [h]
  exact P2mSectionIntegralB.lintegral_enorm_mul_lt_top T μ τ hT F hFm hC hFT w hw0 hwm hwc hw1
