import Tengoku.Seed.MeasureTheory.Measure.Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Elementary API for measures supported on a compact real interval -/

open Set
open MeasureTheory

namespace MeasureTheory.Measure

/-- A law whose support is contained in a real interval is almost surely
in that interval.
@isnad1 id=eventual.1h3v.s5.5330d05b517d from=translated src=- shape=1c4284b9 vocab=4595f954
-/
theorem ae_mem_Icc_of_support_subset (μ : Measure ℝ) {a b : ℝ}
    (hsupport : μ.support ⊆ Icc a b) : ∀ᵐ z ∂μ, z ∈ Icc a b :=
  (show ∀ᵐ z ∂μ, z ∈ μ.support from μ.support_mem_ae).mono hsupport

/-- The support of a real interval-supported measure is compact.
@isnad1 id=iscompac.1h3v.s5.e30c9d288087 from=translated src=- shape=df5d90d8 vocab=cfd1f8ed
-/
theorem isCompact_support_of_subset_Icc (μ : Measure ℝ) {a b : ℝ}
    (hsupport : μ.support ⊆ Icc a b) : IsCompact μ.support :=
  isCompact_Icc.of_isClosed_subset μ.isClosed_support hsupport

end MeasureTheory.Measure
