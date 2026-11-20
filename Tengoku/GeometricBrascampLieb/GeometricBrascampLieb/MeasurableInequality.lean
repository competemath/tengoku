import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.IntegrableInequality
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.MeasurableTruncation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The geometric Brascamp–Lieb inequality with sharp constant one

This proves the original extended nonnegative integral statement for arbitrary
measurable inputs, including infinite integrals, zero masses and zero weights.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F)

/-- Geometric Brascamp–Lieb for arbitrary extended nonnegative measurable functions.
@isnad1 id=le.1h5v.s9.7379077a0e41 from=translated src=- shape=c08a8158 vocab=f9a26697
-/
theorem lintegral_prod_le (f : ∀ i, F i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, (f i (D.map i x))^D.weight i) ≤
      ∏ i, (∫⁻ y, f i y)^D.weight i := by
  let u := fun n x => ∏ i, (boundedTruncation (f i) n (D.map i x))^D.weight i
  have hmono (i : ι) (x : E) :
      Monotone (fun n => (boundedTruncation (f i) n (D.map i x))^D.weight i) :=
    fun _ _ h => ENNReal.rpow_le_rpow (boundedTruncation_monotone (f i) _ h) (D.weight_nonneg i)
  have hpoint (x : E) : (∏ i, (f i (D.map i x))^D.weight i) = ⨆ n, u n x := by
    have he (i : ι) : (⨆ n, (boundedTruncation (f i) n (D.map i x))^D.weight i) =
        (f i (D.map i x))^D.weight i := by
      rw [iSup_ennreal_rpow_of_monotone _ (boundedTruncation_monotone (f i) _) (D.weight_nonneg i),
        iSup_boundedTruncation]
    have h := prod_iSup_ennreal_of_monotone Finset.univ
      (fun i n => (boundedTruncation (f i) n (D.map i x))^D.weight i) (fun i => hmono i x)
    simpa only [he] using h
  have hmeas (n : ℕ) : Measurable (u n) := by
    apply Finset.measurable_fun_prod
    intro i _
    exact (ENNReal.continuous_rpow_const (y := D.weight i)).measurable.comp
      ((boundedTruncation_measurable (hf i) n).comp (D.map i).continuous.measurable)
  have hbound (n : ℕ) : (∫⁻ x, u n x) ≤ ∏ i, (∫⁻ y, f i y)^D.weight i := by
    have h := D.lintegral_prod_le_integrable
      (fun i => boundedTruncation_toReal_integrable (hf i) n)
      (fun i y => ENNReal.toReal_nonneg)
    simp_rw [ENNReal.ofReal_toReal (boundedTruncation_ne_top _ _ _)] at h
    apply h.trans
    exact Finset.prod_le_prod' fun i _ => ENNReal.rpow_le_rpow
      (lintegral_mono (boundedTruncation_le (f i) n)) (D.weight_nonneg i)
  calc
    _ = ∫⁻ x, ⨆ n, u n x := lintegral_congr (fun x => hpoint x)
    _ = ⨆ n, ∫⁻ x, u n x := lintegral_iSup hmeas
      (fun m n h x => Finset.prod_le_prod' fun i _ => hmono i x h)
    _ ≤ _ := iSup_le hbound

/-- The original project goal, now proved from the two geometric identities.
@isnad1 id=integral.0h4v.s7.35c6ede22d97 from=translated src=- shape=eaa0867c vocab=7b963416
-/
theorem integralInequality : D.IntegralInequality := D.lintegral_prod_le

end GeometricBrascampLieb.Datum
