/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import Tengoku.SplittingDensityRationality.SurfaceBlowup.Measure.AdicTransport
import Tengoku.SplittingDensityRationality.SurfaceBlowup.Unramified.FrobeniusDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measure-preserving maps between homogeneous cells

Over a complete discrete valuation ring `O` with finite residue field, the normalized Haar measures
on residue cells of monic polynomials, on reduced form cells and on projective cells are related by
explicit algebraic maps. This file shows that these maps are measure preserving.

## Main results

* `SurfaceBlowup.form_product_measurable`: the reduced form-product map is Borel measurable.
* `SurfaceBlowup.factor_cells_measure_preserving`: multiplying monic lifts of pairwise coprime
  residue factors pushes the product of the factor cell measures to the cell measure of the product.
* `SurfaceBlowup.form_cell_monic_identification`: reduced form cells normalized at the last
  coordinate are monic residue cells, and coordinate reversal identifies the form cell of `X ^ r`
  normalized at `0` with the monic residue cell of `X ^ r`, measure-preservingly.
* `SurfaceBlowup.form_cells_measure_preserving`: the homogeneous analogue of the first result for
  reduced form cells.
* `SurfaceBlowup.projective_cell_normalization_pushforward`: normalizing a primitive vector at a
  coordinate where its residue form is `1` pushes the projective cell measure to the reduced form
  cell measure.

## Implementation notes

The three measure-preservation proofs share one skeleton
(`measurePreserving_cellMeasure_of_balls`): both measures are finite and agree on the
generating `𝔪`-adic balls, which reduces to balls of radius `𝔪 ^ L`, `L ≥ 1`, centred in the
target cell (balls centred outside the cell miss it).

Provenance: `Thm_SurfaceBlowupV2_{form_product_measurable, factor_cells_measure_preserving,
form_cell_monic_identification, form_cells_measure_preserving,
projective_cell_normalization_pushforward}` (`form_product_measurable` moved from
`Unramified/LocalDescent.lean`).
-/

namespace SurfaceBlowup

open scoped BigOperators ENNReal

/-! ### A skeleton for measure preservation onto a cell -/

/-! ### Products of monic residue cells -/

/-! ### Reduced form cells versus monic residue cells -/

/-! ### Measurability of form products -/

/-- The reduced form-product map is Borel measurable.-/
theorem form_product_measurable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1) (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1))
    (hμ : formProd d g μ = 1) :
    Measurable (reducedFormProduct O d ν g μ) := by
  set m := IsLocalRing.maximalIdeal O
  set f := reducedFormProduct O d ν g μ
  set PC : Set (∀ i, Fin (d i) → O) :=
    Set.pi Set.univ (fun i ↦ reducedFormCell O (d i) (ν i) (g i))
  have hPC : MeasurableSet PC := MeasurableSet.univ_pi (fun i ↦
    (normalized_form_cell_cylinder_mass O htop (d i) (ν i) (g i) (hgν i)).2.2.2.1)
  have hoff : ∀ a, a ∉ PC → f a = 0 := fun a ha ↦ by
    simp only [f, reducedFormProduct]
    exact ite_eq_right fun h ↦ ha fun i _ ↦ h i
  have hball : ∀ (k : ℕ) (L : ℕ) (x : Fin k → O),
      MeasurableSet {b : Fin k → O | ∀ j, b j - x j ∈ m ^ L} := fun k L x ↦ by
    have hk := finite_coordinate_borel_cylinders O m htop k
    have : @MeasurableSet _ (adicCylinderSpace m (Fin k → O)) {b | adicCongr m L b x} :=
      MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨L, x, rfl⟩)
    rw [← hk] at this
    convert this using 1
    ext b
    exact (finite_coordinate_adic_congruence O k m L b x).symm
  have hk := finite_coordinate_borel_cylinders O m htop (∑ i, d i)
  change @Measurable _ _ _ (inferInstance : MeasurableSpace (Fin _ → O)) f
  rw [hk]
  refine measurable_generateFrom ?_
  rintro s (rfl | ⟨L, x, rfl⟩)
  · simp
  obtain ⟨_, hsymm, htrans, -, -⟩ := adic_congruence_rules O (Fin (∑ i, d i) → O) m
  by_cases hne : ∃ a₀ ∈ PC, adicCongr m L (f a₀) x
  · obtain ⟨a₀, ha₀, hfa₀⟩ := hne
    have heq : f ⁻¹' {y | adicCongr m L y x} =
        (PC ∩ Set.pi Set.univ (fun i ↦ {b : Fin (d i) → O | ∀ j, b j - a₀ i j ∈ m ^ L})) ∪
        (PCᶜ ∩ {_a | adicCongr m L (0 : Fin (∑ i, d i) → O) x}) := by
      ext a
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_univ_pi]
      by_cases ha : a ∈ PC
      · simp only [ha, true_and, not_true_eq_false, false_and, or_false]
        constructor
        · intro h
          have h2 : adicCongr m L (f a) (f a₀) := htrans _ _ _ _ h (hsymm _ _ _ hfa₀)
          rw [finite_coordinate_adic_congruence] at h2
          exact form_product_congruence_reflects O ι d ν g hgν hc μ hμ a a₀ ha ha₀ L h2
        · intro h
          refine htrans _ _ _ _ ?_ hfa₀
          rw [finite_coordinate_adic_congruence]
          exact (form_product_maps_to_and_preserves O ι d ν g μ hμ a a₀ ha ha₀).2.2.2 L h
      · simp only [ha, false_and, false_or, not_false_eq_true, true_and, hoff a ha]
    rw [heq]
    exact (hPC.inter (MeasurableSet.univ_pi (fun i ↦ hball _ _ _))).union
      (hPC.compl.inter (MeasurableSet.const _))
  · push Not at hne
    have heq : f ⁻¹' {y | adicCongr m L y x} =
        PCᶜ ∩ {_a | adicCongr m L (0 : Fin (∑ i, d i) → O) x} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      by_cases ha : a ∈ PC
      · simp only [ha, not_true_eq_false, false_and, iff_false]
        exact hne a ha
      · simp only [ha, not_false_eq_true, true_and, hoff a ha]
    rw [heq]
    exact hPC.compl.inter (MeasurableSet.const _)

/-! ### Products of reduced form cells -/

/-! ### Projective cells -/

end SurfaceBlowup
