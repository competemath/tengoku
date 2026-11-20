import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.SmallTimeEndpoint
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.LargeTimeEndpoint
import Tengoku.Seed.Analysis.SpecificLimits.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric BL for continuous compactly supported inputs of positive mass

Fatou's lemma transfers the positive-time heat bound to the original inputs.
The general measurable-input theorem, including zero and infinite masses,
is not asserted here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GeometricBrascampLieb

/-- A uniform integral bound passes to a pointwise limit of nonnegative functions.-/
theorem lintegral_ofReal_le_of_pointwise_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hu : ∀ n, Integrable (u n) μ) (hu0 : ∀ n x, 0 ≤ u n x)
    (hbound : ∀ n, ∫ x, u n x ∂μ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
  have hl (x : α) : liminf (fun n => ENNReal.ofReal (u n x)) atTop = ENNReal.ofReal (f x) :=
    ((ENNReal.continuous_ofReal.tendsto _).comp (hlim x)).liminf_eq
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (u n x)) atTop ∂μ := by simp_rw [hl]
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => (hu n).aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal C := by
      have hb : ∀ n, (∫⁻ x, ENNReal.ofReal (u n x) ∂μ) ≤ ENNReal.ofReal C := by
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hu n) (Eventually.of_forall (hu0 n))]
        exact ENNReal.ofReal_le_ofReal (hbound n)
      simpa only [liminf_const] using liminf_le_liminf (f := atTop) (Eventually.of_forall hb)

end GeometricBrascampLieb

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F) {f : ∀ i, F i → ℝ}

/-- The nonnegative integral bound for continuous bounded-support data.-/
theorem lintegral_ofReal_prod_le_of_bounded_support
    (hf : ∀ i, Integrable (f i)) (hfc : ∀ i, Continuous (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hmass : ∀ i, 0 < ∫ y, f i y)
    {C R : ι → ℝ} (hbound : ∀ i y, ‖f i y‖ ≤ C i)
    (hsupport : ∀ i y, f i y ≠ 0 → ‖y‖ ≤ R i) :
    (∫⁻ x, ENNReal.ofReal (∏ i, (f i (D.map i x))^D.weight i)) ≤
      ENNReal.ofReal (∏ i, (∫ y, f i y)^D.weight i) := by
  let τ := fun n : ℕ => 1/((n : ℝ)+1)
  have ht (n : ℕ) : 0 < τ n := by dsimp [τ]; positivity
  have hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ht⟩
  let u := fun n x => ∏ i, (heatConvolution (f i) (τ n) (D.map i x))^D.weight i
  have hi (n : ℕ) : Integrable (u n) := by
    have h := (D.convolution_heatIntegrability hf hf0 hmass hsupport).product_integrable (τ n) (ht n)
    change Integrable (fun x => D.heatProduct
      (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) (τ n) x) at h
    simpa only [D.heatProduct_convolution_eq_prod hf hf0 hmass (ht n)] using h
  have hnonneg (n : ℕ) (x : E) : 0 ≤ u n x :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg
      (heatConvolution_pos (hf i) (hf0 i) (hmass i) (ht n) _).le _
  apply lintegral_ofReal_le_of_pointwise_tendsto hi hnonneg
    (fun n => D.integral_prod_heatConvolution_le hf hf0 hmass hsupport (ht n))
  intro x
  apply tendsto_finsetProd
  intro i _
  exact ((heatConvolution_tendsto_zero (hfc i) (hbound i) (D.map i x)).comp hτ).rpow_const
    (Or.inr (D.weight_nonneg i))

/-- The original product is integrable; its real integral is not using the default value for a nonintegrable function.-/
theorem integrable_prod_of_bounded_support
    (hf : ∀ i, Integrable (f i)) (hfc : ∀ i, Continuous (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hmass : ∀ i, 0 < ∫ y, f i y)
    {C R : ι → ℝ} (hbound : ∀ i y, ‖f i y‖ ≤ C i)
    (hsupport : ∀ i y, f i y ≠ 0 → ‖y‖ ≤ R i) :
    Integrable (fun x => ∏ i, (f i (D.map i x))^D.weight i) := by
  have hc : Continuous (fun x => ∏ i, (f i (D.map i x))^D.weight i) :=
    continuous_finsetProd _ fun i _ =>
      ((hfc i).comp (D.map i).continuous).rpow_const (fun _ => Or.inr (D.weight_nonneg i))
  have h0 (x : E) : 0 ≤ ∏ i, (f i (D.map i x))^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hf0 i _) _
  apply (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable
    (Eventually.of_forall h0)).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (D.lintegral_ofReal_prod_le_of_bounded_support hf hfc hf0 hmass hbound hsupport)

/-- The extended nonnegative formulation, for real-valued bounded-support inputs.-/
theorem lintegral_prod_le_of_bounded_support
    (hf : ∀ i, Integrable (f i)) (hfc : ∀ i, Continuous (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hmass : ∀ i, 0 < ∫ y, f i y)
    {C R : ι → ℝ} (hbound : ∀ i y, ‖f i y‖ ≤ C i)
    (hsupport : ∀ i y, f i y ≠ 0 → ‖y‖ ≤ R i) :
    (∫⁻ x, ∏ i, (ENNReal.ofReal (f i (D.map i x)))^D.weight i) ≤
      ∏ i, (∫⁻ y, ENNReal.ofReal (f i y))^D.weight i := by
  have hp (x : E) : ENNReal.ofReal (∏ i, (f i (D.map i x))^D.weight i) =
      ∏ i, (ENNReal.ofReal (f i (D.map i x)))^D.weight i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hf0 i _) _)]
    exact Finset.prod_congr rfl fun i _ =>
      (ENNReal.ofReal_rpow_of_nonneg (hf0 i _) (D.weight_nonneg i)).symm
  have hm : ENNReal.ofReal (∏ i, (∫ y, f i y)^D.weight i) =
      ∏ i, (∫⁻ y, ENNReal.ofReal (f i y))^D.weight i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hmass i).le _)]
    apply Finset.prod_congr rfl
    intro i _
    rw [← ENNReal.ofReal_rpow_of_nonneg (hmass i).le (D.weight_nonneg i),
      ofReal_integral_eq_lintegral_ofReal (hf i) (Eventually.of_forall (hf0 i))]
  simpa only [hp, hm] using
    D.lintegral_ofReal_prod_le_of_bounded_support hf hfc hf0 hmass hbound hsupport

/-- Geometric BL in the ordinary real integral notation for bounded-support data.-/
theorem integral_prod_le_of_bounded_support
    (hf : ∀ i, Integrable (f i)) (hfc : ∀ i, Continuous (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hmass : ∀ i, 0 < ∫ y, f i y)
    {C R : ι → ℝ} (hbound : ∀ i y, ‖f i y‖ ≤ C i)
    (hsupport : ∀ i y, f i y ≠ 0 → ‖y‖ ≤ R i) :
    (∫ x, ∏ i, (f i (D.map i x))^D.weight i) ≤ ∏ i, (∫ y, f i y)^D.weight i := by
  have hc : Continuous (fun x => ∏ i, (f i (D.map i x))^D.weight i) :=
    continuous_finsetProd _ fun i _ =>
      ((hfc i).comp (D.map i).continuous).rpow_const (fun _ => Or.inr (D.weight_nonneg i))
  have h0 (x : E) : 0 ≤ ∏ i, (f i (D.map i x))^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hf0 i _) _
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hc.aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (D.lintegral_ofReal_prod_le_of_bounded_support hf hfc hf0 hmass hbound hsupport)
  simpa only [ENNReal.toReal_ofReal (Finset.prod_nonneg
    (fun i _ => Real.rpow_nonneg (hmass i).le (D.weight i)))] using h

/-- The sharp inequality for continuous compactly supported nonnegative inputs of positive mass.-/
theorem integral_prod_le_of_hasCompactSupport
    (hfc : ∀ i, Continuous (f i)) (hcompact : ∀ i, HasCompactSupport (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hmass : ∀ i, 0 < ∫ y, f i y) :
    (∫ x, ∏ i, (f i (D.map i x))^D.weight i) ≤ ∏ i, (∫ y, f i y)^D.weight i := by
  have hf (i : ι) : Integrable (f i) := (hfc i).integrable_of_hasCompactSupport (hcompact i)
  choose C hC using fun i => (hcompact i).exists_bound_of_continuous (hfc i)
  have hs (i : ι) : ∃ R : ℝ, ∀ y, f i y ≠ 0 → ‖y‖ ≤ R := by
    obtain ⟨R, hR⟩ := (hcompact i).isBounded.exists_norm_le
    exact ⟨R, fun y hy => hR y (subset_tsupport (f i) hy)⟩
  choose R hR using hs
  exact D.integral_prod_le_of_bounded_support hf hfc hf0 hmass hC hR

end GeometricBrascampLieb.Datum
