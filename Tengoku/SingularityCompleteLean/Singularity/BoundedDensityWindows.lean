import Tengoku.SingularityCompleteLean.Singularity.InvariantRestrictionCocycle
import Tengoku.SingularityCompleteLean.Singularity.LogDensityMeasureComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive-measure windows with bounded logarithmic density

The finite-valued logarithmic density has a bounded window of positive mass.
On a measurable window, equivalent finite measures have the corresponding
restricted exponential comparison. No global density bound is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace Singularity

/-- The logarithmic density window is measurable.
@isnad1 id=measurab.0h4v.s5.c723a6f8c80a from=translated src=- shape=d60eec63 vocab=aca9f4c2
-/
theorem measurableSet_logDensity_window {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) (M : ℝ) :
    MeasurableSet {ξ | |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ M} := by
  simpa only [Real.norm_eq_abs] using
    measurableSet_le (Measure.measurable_rnDeriv ν m).ennreal_toReal.log.norm
      (measurable_const (a := M))

/-- Every nonzero measure has a positive-mass window for its real
logarithmic density relative to any reference measure.
@isnad1 id=ex.1h3v.s6.2ead94cee0e8 from=translated src=- shape=9b5a8421 vocab=dde84ea0
-/
theorem exists_positive_logDensity_window {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) (hν : 0 < ν univ) :
    ∃ M : ℝ, 0 ≤ M ∧ 0 < ν {ξ | |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ M} := by
  have hcover : (⋃ n : ℕ, {ξ | |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ (n : ℝ)}) = univ := by
    apply eq_univ_of_forall
    intro ξ
    obtain ⟨n, hn⟩ := exists_nat_ge |Real.log ((ν.rnDeriv m ξ).toReal)|
    exact mem_iUnion.mpr ⟨n, hn⟩
  by_contra hnone
  have hzero (n : ℕ) : ν {ξ | |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ (n : ℝ)} = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_not_gt
    intro hp
    exact hnone ⟨n, Nat.cast_nonneg n, hp⟩
  have h := measure_iUnion_null hzero
  rw [hcover] at h
  exact hν.ne' h

/-- A bound on the log density on E compares the restrictions of two
finite equivalent measures, without any bound outside E.
@isnad1 id=and.4h5v.s7.778969e9c87a from=translated src=- shape=8f4b2979 vocab=510a6c84
-/
theorem restricted_measure_comparison_of_logDensity_window
    {B : Type*} [MeasurableSpace B] (ν m : Measure B)
    [IsFiniteMeasure ν] [IsFiniteMeasure m]
    (hac : ν ≪ m) (hreverse : m ≪ ν) {E : Set B} (hE : MeasurableSet E)
    (M : ℝ) (hwindow : ∀ ξ ∈ E, |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ M) :
    ENNReal.ofReal (Real.exp (-M)) • m.restrict E ≤ ν.restrict E ∧
      ν.restrict E ≤ ENNReal.ofReal (Real.exp M) • m.restrict E := by
  apply measure_exp_comparison_of_logDensity_bound (ν.restrict E) (m.restrict E)
    (hac.restrict E) (hreverse.restrict E) M
  have hd := (hac.restrict E).ae_le
    (rnDeriv_restrict_both_of_absolutelyContinuous ν m hac hE)
  filter_upwards [hd, ae_restrict_mem hE] with ξ hξ hmem
  rw [hξ]
  exact hwindow ξ hmem

end Singularity
