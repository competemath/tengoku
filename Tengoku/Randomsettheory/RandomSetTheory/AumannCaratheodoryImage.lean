/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableLifting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Carathéodory images of the Aumann expectation

This file gives the general measurable-lifting principle behind exact image
formulas for the Aumann expectation.  If `S` is Effros measurable with compact
nonempty values and `φ (ω, ·)` is a jointly measurable Carathéodory map, every
integrable selection of the image correspondence `φ (ω, ·) '' S ω` can be
lifted to a measurable selection of `S`.

An integrable envelope on `S` makes the lifted selection integrable.  This
yields an exact characterization of the Aumann expectation of the image in
terms of integrals of transformed source selections.  Continuous linear and
affine image formulas are special cases.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory
open Set

noncomputable section

namespace RandomSetTheory

variable {Ω X Y : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

/-- An integrable selection of a Carathéodory image correspondence has an
integrable source selection lift.  The transformed lift agrees with the
given image selection almost everywhere and is itself integrable.
@isnad1 id=ex.8h8v.s8.8d4ce5a2e7bb from=translated src=- shape=effbb865 vocab=a5251cfd
-/
theorem IsIntegrableSelection.exists_lift_caratheodory_image
    {μ : Measure Ω} {S : Ω → Set X} {v : Ω → Y}
    {φ : Ω × X → Y}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (hv : IsIntegrableSelection μ
      (fun ω => (fun x => φ (ω, x)) '' S ω) v) :
    ∃ f : Ω → X,
      IsIntegrableSelection μ S f ∧
      Integrable (fun ω => φ (ω, f ω)) μ ∧
      ∀ᵐ ω ∂μ, φ (ω, f ω) = v ω := by
  let v' : Ω → Y := hv.1.aestronglyMeasurable.mk v
  have hv'meas : Measurable v' :=
    hv.1.aestronglyMeasurable.measurable_mk
  have hvv' : v =ᵐ[μ] v' :=
    hv.1.aestronglyMeasurable.ae_eq_mk
  have hv'mem :
      ∀ᵐ ω ∂μ, v' ω ∈ (fun x => φ (ω, x)) '' S ω := by
    filter_upwards [hv.2, hvv'] with ω hvω heq
    rw [← heq]
    exact hvω
  obtain ⟨f, hfmeas, hfmem, hφfv'⟩ :=
    exists_measurable_lifting_of_ae_mem_image
      hS hcompact hne hφmeas hφcont hv'meas hv'mem
  have hfint : Integrable f μ := by
    apply hg.mono' hfmeas.aestronglyMeasurable
    filter_upwards [hdom] with ω hdomω
    exact hdomω (f ω) (hfmem ω)
  have hφfv : ∀ᵐ ω ∂μ, φ (ω, f ω) = v ω := by
    filter_upwards [hφfv', hvv'] with ω hφfv'ω hvv'ω
    exact hφfv'ω.trans hvv'ω.symm
  have hφfint : Integrable (fun ω => φ (ω, f ω)) μ :=
    hv.1.congr (Filter.EventuallyEq.symm hφfv)
  exact ⟨f, ⟨hfint, Filter.Eventually.of_forall hfmem⟩,
    hφfint, hφfv⟩

/-- **Aumann--Carathéodory image formula.**  The Aumann expectation of a
Carathéodory image correspondence is exactly the set of integrals of
integrable transformed source selections.
@isnad1 id=eq.7h7v.s8.4f54865c9554 from=translated src=- shape=b25d95cc vocab=1777f914
-/
theorem aumannExpectation_caratheodory_image
    [NormedSpace ℝ Y]
    {μ : Measure Ω} {S : Ω → Set X} {φ : Ω × X → Y}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    aumannExpectation μ
        (fun ω => (fun x => φ (ω, x)) '' S ω) =
      {y | ∃ f : Ω → X,
        IsIntegrableSelection μ S f ∧
        Integrable (fun ω => φ (ω, f ω)) μ ∧
        ∫ ω, φ (ω, f ω) ∂μ = y} := by
  apply Set.Subset.antisymm
  · rintro y ⟨v, hv, rfl⟩
    obtain ⟨f, hf, hφfint, hφfv⟩ :=
      hv.exists_lift_caratheodory_image
        hS hcompact hne hφmeas hφcont hg hdom
    exact ⟨f, hf, hφfint, integral_congr_ae hφfv⟩
  · rintro y ⟨f, hf, hφfint, rfl⟩
    refine ⟨fun ω => φ (ω, f ω), ⟨hφfint, ?_⟩, rfl⟩
    filter_upwards [hf.2] with ω hfω
    exact ⟨f ω, hfω, rfl⟩

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
