/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Aumann expectations on finite full-support spaces

On a finite measurable space whose measure gives positive mass to every
point, an almost-everywhere selection is an everywhere selection.  The
Bochner integral is then a finite weighted sum.  Consequently, the Aumann
expectation of a compact-valued correspondence is the continuous image of a
compact product and is itself compact (hence closed), without inserting a
topological closure in its definition.

This is the complete finite-atomic version of the classical Aumann
closedness theorem.  It requires neither convexity nor finite dimensionality
of the range.  The full-support assumption is what makes the pointwise
product representation exact: values over null atoms are otherwise ignored
by both the selection condition and the integral.
-/

open MeasureTheory Set

noncomputable section

namespace RandomSetTheory

variable {Omega E : Type*} [MeasurableSpace Omega]
  [Finite Omega] [MeasurableSingletonClass Omega]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- The finite weighted sum which computes the Bochner integral on a finite
measurable space.-/
def finiteWeightedIntegral (mu : Measure Omega) (f : Omega -> E) : E :=
  letI := Fintype.ofFinite Omega
  ∑ omega, mu.real {omega} • f omega

/--
@isnad1 id=eq.0h4v.s6.54e287e85449 from=translated src=- shape=174cf676 vocab=1ecf3bb1
-/
theorem integral_eq_finiteWeightedIntegral
    {mu : Measure Omega} [IsFiniteMeasure mu] (f : Omega -> E) :
    (∫ omega, f omega ∂mu) = finiteWeightedIntegral mu f := by
  letI := Fintype.ofFinite Omega
  exact MeasureTheory.integral_fintype Integrable.of_finite

/-- On a finite full-support measure space, the Aumann expectation is exactly
the image, under the weighted-sum map, of the product of the pointwise
values.
@isnad1 id=eq.1h4v.s6.0dcff82bbfcc from=translated src=- shape=5c51e378 vocab=29320e9a
-/
theorem aumannExpectation_eq_image_finiteWeightedIntegral
    {mu : Measure Omega} [IsFiniteMeasure mu] {S : Omega -> Set E}
    (hfull : ∀ omega, mu {omega} ≠ 0) :
    aumannExpectation mu S =
      finiteWeightedIntegral mu '' Set.pi Set.univ S := by
  ext x
  constructor
  · rintro ⟨f, hf, hfx⟩
    have hf_pointwise : ∀ omega, f omega ∈ S omega := by
      intro omega
      exact (ae_iff_of_countable.mp hf.2) omega (hfull omega)
    refine ⟨f, ?_, ?_⟩
    · simpa only [Set.mem_pi, Set.mem_univ, forall_const] using hf_pointwise
    · rw [← integral_eq_finiteWeightedIntegral f]
      exact hfx
  · rintro ⟨f, hfS, rfl⟩
    have hf_pointwise : ∀ omega, f omega ∈ S omega := by
      simpa only [Set.mem_pi, Set.mem_univ, forall_const] using hfS
    refine ⟨f, ⟨Integrable.of_finite, ?_⟩, ?_⟩
    · exact Filter.Eventually.of_forall hf_pointwise
    · exact integral_eq_finiteWeightedIntegral f

omit [MeasurableSingletonClass Omega] [CompleteSpace E] in
/--
@isnad1 id=continuo.0h3v.s5.737973146628 from=translated src=- shape=05095dee vocab=59bdc24f
-/
theorem continuous_finiteWeightedIntegral (mu : Measure Omega) :
    Continuous (finiteWeightedIntegral (E := E) mu) := by
  letI := Fintype.ofFinite Omega
  change Continuous (fun f : Omega -> E =>
    ∑ omega, mu.real {omega} • f omega)
  apply continuous_finsetSum Finset.univ
  intro omega _
  exact (continuous_apply omega).const_smul _

/-- Finite-atomic Aumann compactness, before taking any closure.  Compactness
of the fibers is the only topological hypothesis; nonemptiness and convexity
are not needed for the conclusion.
@isnad1 id=iscompac.2h4v.s6.64f8aa8a98b9 from=translated src=- shape=74276896 vocab=57fb2322
-/
theorem aumannExpectation_isCompact_of_finite_fullSupport
    {mu : Measure Omega} [IsFiniteMeasure mu] {S : Omega -> Set E}
    (hfull : ∀ omega, mu {omega} ≠ 0)
    (hcompact : ∀ omega, IsCompact (S omega)) :
    IsCompact (aumannExpectation mu S) := by
  rw [aumannExpectation_eq_image_finiteWeightedIntegral hfull]
  exact (isCompact_univ_pi hcompact).image
    (continuous_finiteWeightedIntegral mu)

/-- In particular, finite-atomic Aumann expectations of compact-valued
correspondences are closed without a `closure` wrapper.
@isnad1 id=isclosed.2h4v.s6.9013ace61d78 from=translated src=- shape=fc0e45b7 vocab=ae3bd840
-/
theorem aumannExpectation_isClosed_of_finite_fullSupport
    {mu : Measure Omega} [IsFiniteMeasure mu] {S : Omega -> Set E}
    (hfull : ∀ omega, mu {omega} ≠ 0)
    (hcompact : ∀ omega, IsCompact (S omega)) :
    IsClosed (aumannExpectation mu S) :=
  (aumannExpectation_isCompact_of_finite_fullSupport hfull hcompact).isClosed

/-- The closure used in the general theory disappears on finite full-support
spaces.
@isnad1 id=eq.2h4v.s7.dce1abf6f49f from=translated src=- shape=88cc9182 vocab=6f6c3578
-/
theorem closure_aumannExpectation_eq_of_finite_fullSupport
    {mu : Measure Omega} [IsFiniteMeasure mu] {S : Omega -> Set E}
    (hfull : ∀ omega, mu {omega} ≠ 0)
    (hcompact : ∀ omega, IsCompact (S omega)) :
    closure (aumannExpectation mu S) = aumannExpectation mu S :=
  (aumannExpectation_isClosed_of_finite_fullSupport hfull hcompact).closure_eq

/-- Compactness and nonemptiness of the finite-atomic Aumann expectation.
The latter follows from a pointwise choice and needs no measurable-selection
theorem because the source is finite and discrete.
@isnad1 id=and.3h4v.s7.636e9e6dae79 from=translated src=- shape=741b87d1 vocab=4058b921
-/
theorem aumannExpectation_isCompact_nonempty_of_finite_fullSupport
    {mu : Measure Omega} [IsFiniteMeasure mu] {S : Omega -> Set E}
    (hfull : ∀ omega, mu {omega} ≠ 0)
    (hcompact : ∀ omega, IsCompact (S omega))
    (hne : ∀ omega, (S omega).Nonempty) :
    IsCompact (aumannExpectation mu S) ∧
      (aumannExpectation mu S).Nonempty := by
  refine ⟨aumannExpectation_isCompact_of_finite_fullSupport hfull hcompact, ?_⟩
  choose f hf using hne
  exact aumannExpectation_nonempty_of_selection
    ⟨Integrable.of_finite, Filter.Eventually.of_forall hf⟩

end RandomSetTheory
