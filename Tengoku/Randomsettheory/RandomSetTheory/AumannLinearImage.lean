/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannLinearTransport
import Tengoku.Randomsettheory.RandomSetTheory.AumannCaratheodoryImage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact linear images of the Aumann expectation

For an arbitrary continuous linear map, functoriality of the Bochner
integral immediately gives one inclusion between the image of an Aumann
expectation and the Aumann expectation of the pointwise image.  The converse
does not follow from linear algebra alone: a measurable selection of the
image correspondence has to be lifted measurably through the linear map.

This file obtains that lifting from the exact Carathéodory-image lifting
theorem.  Compact nonempty Effros-measurable fibres guarantee a measurable
lift, while an integrable envelope of the source correspondence guarantees
that the lift is integrable.  Consequently, Aumann expectation commutes
exactly with every continuous linear map, without injectivity, surjectivity,
or a continuous linear inverse.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory
open Set
open scoped Pointwise

noncomputable section

namespace RandomSetTheory

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-! ## Integrable lifting through a continuous linear map -/

/-- Every integrable selection of the pointwise continuous-linear image of a
compact Effros correspondence admits an integrable selection lift.  The
linear identity is required only almost everywhere, which is the natural
notion for both Bochner integration and Aumann expectation.-/
theorem IsIntegrableSelection.exists_lift_continuousLinearMap
    {μ : Measure Ω} {S : Ω → Set E} {v : Ω → F}
    (L : E →L[ℝ] F)
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (hv : IsIntegrableSelection μ (fun ω => L '' S ω) v) :
    ∃ f : Ω → E, IsIntegrableSelection μ S f ∧
      ∀ᵐ ω ∂μ, L (f ω) = v ω := by
  obtain ⟨f, hf, _, hLf⟩ :=
    hv.exists_lift_caratheodory_image
      hS hcompact hne
      (L.measurable.comp measurable_snd) (fun _ => L.continuous)
      hg hdom
  exact ⟨f, hf, hLf⟩

/-! ## Exact commutation with Aumann expectation -/

/-- **Exact linear-image theorem for the Aumann expectation.**

Under compact nonempty Effros measurability and an integrable envelope of the
source fibres, Aumann expectation commutes with every continuous linear map.
No injectivity, surjectivity, or closed-range assumption is needed.-/
theorem aumannExpectation_image_continuousLinearMap
    [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E}
    (L : E →L[ℝ] F)
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    aumannExpectation μ (fun ω => L '' S ω) =
      L '' aumannExpectation μ S := by
  apply Set.Subset.antisymm
  · rintro y ⟨v, hv, rfl⟩
    obtain ⟨f, hf, hLf⟩ :=
      hv.exists_lift_continuousLinearMap L hS hcompact hne hg hdom
    refine ⟨∫ ω, f ω ∂μ, ⟨f, hf, rfl⟩, ?_⟩
    calc
      L (∫ ω, f ω ∂μ) = ∫ ω, L (f ω) ∂μ :=
        (L.integral_comp_comm hf.1).symm
      _ = ∫ ω, v ω ∂μ := integral_congr_ae hLf
  · exact image_aumannExpectation_subset_aumannExpectation_image L

/-- Exact affine image formula with a random integrable translation.  The
translation may depend on `ω`; its contribution to the expectation is its
Bochner integral.-/
theorem aumannExpectation_affine_image_continuousLinearMap
    [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E} {b : Ω → F}
    (L : E →L[ℝ] F)
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (hb : Integrable b μ) :
    aumannExpectation μ
        (fun ω => (fun x => L x + b ω) '' S ω) =
      (fun x => L x + ∫ ω, b ω ∂μ) '' aumannExpectation μ S := by
  have himage :
      (fun ω => (fun x => L x + b ω) '' S ω) =
        (fun ω => L '' S ω + ({b ω} : Set F)) := by
    funext ω
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨L x, ⟨x, hx, rfl⟩, b ω, Set.mem_singleton _, rfl⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, t, ht, hzt⟩
      simp only [Set.mem_singleton_iff] at ht
      subst t
      exact ⟨x, hx, hzt⟩
  rw [himage, aumannExpectation_add_singleton hb,
    aumannExpectation_image_continuousLinearMap L hS hcompact hne hg hdom]
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, t, ht, hzt⟩
    simp only [Set.mem_singleton_iff] at ht
    subst t
    exact ⟨x, hx, hzt⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨L x, ⟨x, hx, rfl⟩, ∫ ω, b ω ∂μ,
      Set.mem_singleton _, rfl⟩

/-- The closure of the image of the closed source Aumann expectation and the
closure of the image Aumann expectation coincide.  Closing both sides is
essential in general because a continuous linear map may have nonclosed
range.-/
theorem closure_image_closure_aumannExpectation_continuousLinearMap
    [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E}
    (L : E →L[ℝ] F)
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    closure (L '' closure (aumannExpectation μ S)) =
      closure (aumannExpectation μ (fun ω => L '' S ω)) := by
  rw [aumannExpectation_image_continuousLinearMap L hS hcompact hne hg hdom]
  apply Set.Subset.antisymm
  · apply closure_minimal
    · exact image_closure_subset_closure_image L.continuous
    · exact isClosed_closure
  · exact closure_mono (Set.image_mono subset_closure)

/-- Closed convexification is unchanged if one first closed-convexifies the
source Aumann expectation before applying the continuous linear map.  The
outer closed convex hull accounts for a possibly nonclosed image.-/
theorem closedConvexHull_image_closedConvexHull_aumannExpectation_continuousLinearMap
    [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E}
    (L : E →L[ℝ] F)
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    closedConvexHull ℝ
        (L '' closedConvexHull ℝ (aumannExpectation μ S)) =
      closedConvexHull ℝ
        (aumannExpectation μ (fun ω => L '' S ω)) := by
  have hEq :=
    aumannExpectation_image_continuousLinearMap L hS hcompact hne hg hdom
  apply Set.Subset.antisymm
  · apply closedConvexHull_min
    · exact image_closedConvexHull_aumannExpectation_subset L
    · exact convex_closedConvexHull
    · exact isClosed_closedConvexHull
  · rw [hEq]
    apply closedConvexHull_min
    · rintro _ ⟨x, hx, rfl⟩
      apply subset_closedConvexHull (𝕜 := ℝ)
      exact ⟨x, subset_closedConvexHull (𝕜 := ℝ) hx, rfl⟩
    · exact convex_closedConvexHull
    · exact isClosed_closedConvexHull

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
