import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.CompactPerturbation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric BL for all nonnegative continuous compactly supported inputs

A positive compact perturbation removes the positive-mass hypothesis. This
also handles zero-weight inputs of zero mass without changing the datum.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F) {f : ∀ i, F i → ℝ}

/--
@isnad1 id=le.4h5v.s9.0267103362ef from=translated src=- shape=bb033431 vocab=39214977
-/
theorem lintegral_ofReal_prod_le_compact_of_pos
    (hfc : ∀ i, Continuous (f i)) (hcompact : ∀ i, HasCompactSupport (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hmass : ∀ i, 0 < ∫ y, f i y) :
    (∫⁻ x, ENNReal.ofReal (∏ i, (f i (D.map i x))^D.weight i)) ≤
      ENNReal.ofReal (∏ i, (∫ y, f i y)^D.weight i) := by
  have hf (i : ι) : Integrable (f i) := (hfc i).integrable_of_hasCompactSupport (hcompact i)
  choose C hC using fun i => (hcompact i).exists_bound_of_continuous (hfc i)
  have hs (i : ι) : ∃ R : ℝ, ∀ y, f i y ≠ 0 → ‖y‖ ≤ R := by
    obtain ⟨R, hR⟩ := (hcompact i).isBounded.exists_norm_le
    exact ⟨R, fun y hy => hR y (subset_tsupport (f i) hy)⟩
  choose R hR using hs
  exact D.lintegral_ofReal_prod_le_of_bounded_support hf hfc hf0 hmass hC hR

/-- The nonnegative integral bound with no positive-mass hypothesis.
@isnad1 id=le.3h5v.s9.d91e89a4bf7a from=translated src=- shape=2fe6128f vocab=a689613f
-/
theorem lintegral_ofReal_prod_le_continuous_compact
    (hfc : ∀ i, Continuous (f i)) (hcompact : ∀ i, HasCompactSupport (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) :
    (∫⁻ x, ENNReal.ofReal (∏ i, (f i (D.map i x))^D.weight i)) ≤
      ENNReal.ofReal (∏ i, (∫ y, f i y)^D.weight i) := by
  have hf (i : ι) : Integrable (f i) := (hfc i).integrable_of_hasCompactSupport (hcompact i)
  have hc : Continuous (fun e : ℝ => ENNReal.ofReal
      (∏ i, ((∫ y, f i y)+e*(∫ y : F i, unitTent y))^D.weight i)) := by
    apply ENNReal.continuous_ofReal.comp
    apply continuous_finsetProd
    intro i _
    exact (continuous_const.add (continuous_id.mul continuous_const)).rpow_const
      (fun _ => Or.inr (D.weight_nonneg i))
  have hlim := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [zero_mul, add_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with e (he : 0 < e)
  let g := fun i => compactPerturbation (f i) e
  have hg0 (i : ι) (y : F i) : 0 ≤ g i y := (hf0 i y).trans (le_compactPerturbation _ he.le y)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (∏ i, (g i (D.map i x))^D.weight i) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      exact Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hf0 i _) _)
        (fun i _ => Real.rpow_le_rpow (hf0 i _) (le_compactPerturbation _ he.le _) (D.weight_nonneg i))
    _ ≤ ENNReal.ofReal (∏ i, (∫ y, g i y)^D.weight i) :=
      D.lintegral_ofReal_prod_le_compact_of_pos
        (fun i => compactPerturbation_continuous (hfc i) e)
        (fun i => compactPerturbation_hasCompactSupport (hcompact i) e) hg0
        (fun i => integral_compactPerturbation_pos (hf i) (hf0 i) he)
    _ = _ := by simp only [g, integral_compactPerturbation (hf _)]

/-- The original product is integrable, including zero-mass and zero-weight cases.
@isnad1 id=integrab.3h5v.s9.8c1e5275007b from=translated src=- shape=efcab13a vocab=a973c5c7
-/
theorem integrable_prod_continuous_compact
    (hfc : ∀ i, Continuous (f i)) (hcompact : ∀ i, HasCompactSupport (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) :
    Integrable (fun x => ∏ i, (f i (D.map i x))^D.weight i) := by
  have hc : Continuous (fun x => ∏ i, (f i (D.map i x))^D.weight i) :=
    continuous_finsetProd _ fun i _ =>
      ((hfc i).comp (D.map i).continuous).rpow_const (fun _ => Or.inr (D.weight_nonneg i))
  have h0 (x : E) : 0 ≤ ∏ i, (f i (D.map i x))^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hf0 i _) _
  apply (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable
    (Eventually.of_forall h0)).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (D.lintegral_ofReal_prod_le_continuous_compact hfc hcompact hf0)

/-- Geometric BL for every nonnegative continuous compactly supported real input.
@isnad1 id=le.3h5v.s9.aa0f82259976 from=translated src=- shape=4f0af827 vocab=a36cf5b9
-/
theorem integral_prod_le_continuous_compact
    (hfc : ∀ i, Continuous (f i)) (hcompact : ∀ i, HasCompactSupport (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) :
    (∫ x, ∏ i, (f i (D.map i x))^D.weight i) ≤ ∏ i, (∫ y, f i y)^D.weight i := by
  have hi := D.integrable_prod_continuous_compact hfc hcompact hf0
  have h0 (x : E) : 0 ≤ ∏ i, (f i (D.map i x))^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hf0 i _) _
  have hb0 : 0 ≤ ∏ i, (∫ y, f i y)^D.weight i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (integral_nonneg (hf0 i)) _
  have h := D.lintegral_ofReal_prod_le_continuous_compact hfc hcompact hf0
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall h0)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hb0).mp h

/-- The extended nonnegative integral version, with arbitrary nonnegative weights.
@isnad1 id=le.3h5v.s9.426e54cb0504 from=translated src=- shape=35049597 vocab=6b6bce0c
-/
theorem lintegral_prod_le_continuous_compact
    (hfc : ∀ i, Continuous (f i)) (hcompact : ∀ i, HasCompactSupport (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) :
    (∫⁻ x, ∏ i, (ENNReal.ofReal (f i (D.map i x)))^D.weight i) ≤
      ∏ i, (∫⁻ y, ENNReal.ofReal (f i y))^D.weight i := by
  have hf (i : ι) : Integrable (f i) := (hfc i).integrable_of_hasCompactSupport (hcompact i)
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
  simpa only [hp, hm] using D.lintegral_ofReal_prod_le_continuous_compact hfc hcompact hf0

end GeometricBrascampLieb.Datum
