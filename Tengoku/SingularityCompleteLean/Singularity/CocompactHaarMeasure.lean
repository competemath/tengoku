import Tengoku.SingularityCompleteLean.Singularity.CocompactGroupQuotient
import Tengoku.SingularityCompleteLean.Singularity.QuotientDilationErgodicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual finite ergodic Haar quotient measure

Starting from discreteness and compactness of Γ\ℍ, choose the constructed
measurable fundamental domain and push forward restricted Haar measure.
Its finiteness, nonzero mass, invariance and diagonal ergodicity are proved;
none of them is supplied as a quotient-measure assumption.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

attribute [local instance] slTwo_locallyCompactSpace slTwo_polishSpace

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
  (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν]

/-- A measurable finite fundamental domain supplied by cocompactness.-/
def cocompactHaarDomain : Set SL(2, ℝ) :=
  (exists_cocompact_finite_fundamentalDomain Γ ν).choose

/--
@isnad1 id=measurab.0h2v.s10.3f7dfe96125a from=translated src=- shape=40949450 vocab=540550e1
-/
theorem cocompactHaarDomain_measurable : MeasurableSet (cocompactHaarDomain Γ ν) :=
  (exists_cocompact_finite_fundamentalDomain Γ ν).choose_spec.1

/--
@isnad1 id=isfundam.0h2v.s10.38f1c14a3a64 from=translated src=- shape=ac66dd74 vocab=b70dfdd8
-/
theorem cocompactHaarDomain_fundamental : IsFundamentalDomain Γ.op (cocompactHaarDomain Γ ν) ν :=
  (exists_cocompact_finite_fundamentalDomain Γ ν).choose_spec.2.1

/--
@isnad1 id=lt.0h2v.s10.6ee9b4f6ee6c from=translated src=- shape=5c298b2b vocab=ffa051d5
-/
theorem cocompactHaarDomain_finite : ν (cocompactHaarDomain Γ ν) < ⊤ :=
  (exists_cocompact_finite_fundamentalDomain Γ ν).choose_spec.2.2

/-- The resulting quotient measure on right cosets.-/
def cocompactHaarQuotientMeasure : Measure (SL(2, ℝ) ⧸ Γ) :=
  (ν.restrict (cocompactHaarDomain Γ ν)).map QuotientGroup.mk

/--
@isnad1 id=isfinite.0h2v.s10.8f1770a36006 from=translated src=- shape=ee388383 vocab=300b161d
-/
theorem cocompactHaarQuotientMeasure_finite :
    IsFiniteMeasure (cocompactHaarQuotientMeasure Γ ν) := by
  let : Fact (ν (cocompactHaarDomain Γ ν) < ⊤) := ⟨cocompactHaarDomain_finite Γ ν⟩
  unfold cocompactHaarQuotientMeasure
  infer_instance

/--
@isnad1 id=eq.0h2v.s11.65866cf09e36 from=translated src=- shape=a50ba646 vocab=236ab756
-/
theorem cocompactHaarQuotientMeasure_univ :
    cocompactHaarQuotientMeasure Γ ν univ = ν (cocompactHaarDomain Γ ν) := by
  have hm : Measurable (QuotientGroup.mk : SL(2, ℝ) → SL(2, ℝ) ⧸ Γ) :=
    measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  rw [cocompactHaarQuotientMeasure, Measure.map_apply hm MeasurableSet.univ]
  simp

/-- The constructed quotient has positive mass.
@isnad1 id=ne.0h2v.s10.f9f7def579c1 from=translated src=- shape=3b826099 vocab=59417ced
-/
theorem cocompactHaarQuotientMeasure_ne_zero : cocompactHaarQuotientMeasure Γ ν ≠ 0 := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := slTwo_haar_rightInvariant ν
  let : Countable Γ := countable_of_Lindelof_of_discrete
  have hp := (cocompactHaarDomain_fundamental Γ ν).measure_ne_zero (NeZero.ne ν)
  intro hzero
  apply hp
  rw [← cocompactHaarQuotientMeasure_univ Γ ν, hzero]
  rfl

/-- The fundamental-domain formula holds for the constructed quotient measure.
@isnad1 id=quotient.0h2v.s11.bb8d9fb9dc99 from=translated src=- shape=184f7648 vocab=878c82d4
-/
theorem cocompactHaarQuotientMeasure_formula :
    QuotientMeasureEqMeasurePreimage ν (cocompactHaarQuotientMeasure Γ ν) := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := slTwo_haar_rightInvariant ν
  let : Countable Γ := countable_of_Lindelof_of_discrete
  exact (cocompactHaarDomain_fundamental Γ ν).quotientMeasureEqMeasurePreimage_quotientMeasure

/-- The constructed quotient measure is invariant under the full special-linear group.
@isnad1 id=smulinva.0h2v.s10.96212042ae18 from=translated src=- shape=b3dfcd39 vocab=d2abd2f1
-/
theorem cocompactHaarQuotientMeasure_invariant :
    SMulInvariantMeasure SL(2, ℝ) (SL(2, ℝ) ⧸ Γ) (cocompactHaarQuotientMeasure Γ ν) := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := cocompactHaarQuotientMeasure_formula Γ ν
  let := (cocompactHaarDomain_fundamental Γ ν).hasFundamentalDomain ν
  exact QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient ν

/-- Positive diagonal times are ergodic for the actual quotient measure.
@isnad1 id=ergodic.1h3v.s11.21e6365edad9 from=translated src=- shape=c1e6483a vocab=bb344795
-/
theorem cocompactHaarQuotientMeasure_dilation_ergodic (τ : ℝ) (hτ : 0 < τ) :
    Ergodic (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • x)
      (cocompactHaarQuotientMeasure Γ ν) :=
  ergodic_dilation_fundamentalDomain Γ ν (cocompactHaarDomain_fundamental Γ ν)
    (cocompactHaarDomain_finite Γ ν) τ hτ

end Singularity
