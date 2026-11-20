import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.L1Approximation
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.NullSetPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric BL for arbitrary nonnegative integrable real inputs

Compact continuous approximations converge almost everywhere and in mass.
Null-set pullback and Fatou's lemma transfer their inequalities to the input.
No continuity, support bound, or positive-mass assumption remains.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GeometricBrascampLieb

theorem lintegral_ofReal_le_of_ae_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : ℕ → α → ℝ} {f : α → ℝ} {C : ℕ → ℝ} {c : ℝ}
    (hu : ∀ n, Integrable (u n) μ) (hu0 : ∀ n x, 0 ≤ u n x)
    (hbound : ∀ n, ∫ x, u n x ∂μ ≤ C n)
    (hC : Tendsto C atTop (𝓝 c))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal c := by
  have hl : ∀ᵐ x ∂μ, liminf (fun n => ENNReal.ofReal (u n x)) atTop = ENNReal.ofReal (f x) :=
    hlim.mono fun x hx => ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (u n x)) atTop ∂μ :=
      lintegral_congr_ae (hl.mono fun x hx => hx.symm)
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => (hu n).aemeasurable.ennreal_ofReal)
    _ ≤ liminf (fun n => ENNReal.ofReal (C n)) atTop := by
      exact liminf_le_liminf (Eventually.of_forall fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal (hu n) (Eventually.of_forall (hu0 n))]
        exact ENNReal.ofReal_le_ofReal (hbound n))
    _ = _ := ((ENNReal.continuous_ofReal.tendsto _).comp hC).liminf_eq

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

/-- The finite nonnegative integral bound for arbitrary nonnegative `L¹` inputs.-/
theorem lintegral_ofReal_prod_le_integrable
    (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i y, 0 ≤ f i y) :
    (∫⁻ x, ENNReal.ofReal (∏ i, (f i (D.map i x))^D.weight i)) ≤
      ENNReal.ofReal (∏ i, (∫ y, f i y)^D.weight i) := by
  choose g hgc hgcompact hg0 hgae hgmass using
    fun i => exists_nonneg_compact_approximation (hf i) (hf0 i)
  have hi (n : ℕ) : Integrable (fun x => ∏ i, (g i n (D.map i x))^D.weight i) :=
    D.integrable_prod_continuous_compact (fun i => hgc i n) (fun i => hgcompact i n) (fun i => hg0 i n)
  have hnonneg (n : ℕ) (x : E) : 0 ≤ ∏ i, (g i n (D.map i x))^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hg0 i n _) _
  have hmass : Tendsto (fun n => ∏ i, (∫ y, g i n y)^D.weight i) atTop
      (𝓝 (∏ i, (∫ y, f i y)^D.weight i)) :=
    tendsto_finsetProd _ fun i _ => (hgmass i).rpow_const (Or.inr (D.weight_nonneg i))
  apply lintegral_ofReal_le_of_ae_tendsto hi hnonneg
    (fun n => D.integral_prod_le_continuous_compact
      (fun i => hgc i n) (fun i => hgcompact i n) (fun i => hg0 i n)) hmass
  have hp (i : ι) : ∀ᵐ x : E, Tendsto (fun n => g i n (D.map i x)) atTop (𝓝 (f i (D.map i x))) :=
    (D.map_quasiMeasurePreserving i).ae (hgae i)
  filter_upwards [ae_all_iff.mpr hp] with x hx
  exact tendsto_finsetProd _ fun i _ => (hx i).rpow_const (Or.inr (D.weight_nonneg i))

theorem aestronglyMeasurable_prod_of_integrable (hf : ∀ i, Integrable (f i)) :
    AEStronglyMeasurable (fun x => ∏ i, (f i (D.map i x))^D.weight i) := by
  apply Finset.aestronglyMeasurable_fun_prod
  intro i _
  exact (Real.continuous_rpow_const (D.weight_nonneg i)).comp_aestronglyMeasurable
    ((hf i).aestronglyMeasurable.comp_quasiMeasurePreserving (D.map_quasiMeasurePreserving i))

/-- Geometric products of nonnegative `L¹` inputs are integrable.-/
theorem integrable_prod_of_integrable (hf : ∀ i, Integrable (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) :
    Integrable (fun x => ∏ i, (f i (D.map i x))^D.weight i) := by
  have h0 (x : E) : 0 ≤ ∏ i, (f i (D.map i x))^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hf0 i _) _
  apply (lintegral_ofReal_ne_top_iff_integrable (D.aestronglyMeasurable_prod_of_integrable hf)
    (Eventually.of_forall h0)).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (D.lintegral_ofReal_prod_le_integrable hf hf0)

/-- The sharp geometric BL inequality for arbitrary nonnegative integrable real functions.-/
theorem integral_prod_le_integrable (hf : ∀ i, Integrable (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) :
    (∫ x, ∏ i, (f i (D.map i x))^D.weight i) ≤ ∏ i, (∫ y, f i y)^D.weight i := by
  have hi := D.integrable_prod_of_integrable hf hf0
  have h0 (x : E) : 0 ≤ ∏ i, (f i (D.map i x))^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hf0 i _) _
  have hb0 : 0 ≤ ∏ i, (∫ y, f i y)^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (integral_nonneg (hf0 i)) _
  have h := D.lintegral_ofReal_prod_le_integrable hf hf0
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall h0)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hb0).mp h

/-- The extended nonnegative integral version for arbitrary nonnegative `L¹` real inputs.-/
theorem lintegral_prod_le_integrable (hf : ∀ i, Integrable (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) :
    (∫⁻ x, ∏ i, (ENNReal.ofReal (f i (D.map i x)))^D.weight i) ≤
      ∏ i, (∫⁻ y, ENNReal.ofReal (f i y))^D.weight i := by
  have hp (x : E) : ENNReal.ofReal (∏ i, (f i (D.map i x))^D.weight i) =
      ∏ i, (ENNReal.ofReal (f i (D.map i x)))^D.weight i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hf0 i _) _)]
    exact Finset.prod_congr rfl fun i _ =>
      (ENNReal.ofReal_rpow_of_nonneg (hf0 i _) (D.weight_nonneg i)).symm
  have hm : ENNReal.ofReal (∏ i, (∫ y, f i y)^D.weight i) =
      ∏ i, (∫⁻ y, ENNReal.ofReal (f i y))^D.weight i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (integral_nonneg (hf0 i)) _)]
    apply Finset.prod_congr rfl
    intro i _
    rw [← ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (hf0 i)) (D.weight_nonneg i),
      ofReal_integral_eq_lintegral_ofReal (hf i) (Eventually.of_forall (hf0 i))]
  simpa only [hp, hm] using D.lintegral_ofReal_prod_le_integrable hf hf0

end GeometricBrascampLieb.Datum
