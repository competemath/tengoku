/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linear transport of the Aumann expectation

This file proves the functoriality of integrable selections and of the Aumann
expectation under continuous linear maps.  A continuous linear map always
gives the forward inclusion.  A continuous linear equivalence gives equality,
because both the selection and its integrability can be transported back by
the inverse equivalence.

The final statements record the corresponding closure and closed-convex-hull
transport rules.  No measurability hypothesis on the correspondence itself is
needed: all measurability information is carried by each integrable selection.
-/

open MeasureTheory
open Set

noncomputable section

namespace RandomSetTheory

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Transport of integrable selections -/

/-- The image of an integrable selection by a continuous linear map is an
integrable selection of the pointwise image correspondence.
@isnad1 id=isintegr.1h7v.s8.70160dc2f1bc from=translated src=- shape=a1093443 vocab=0c9ff64a
-/
theorem IsIntegrableSelection.map_continuousLinearMap
    {μ : Measure Ω} {S : Ω → Set E} {g : Ω → E}
    (L : E →L[ℝ] F) (hg : IsIntegrableSelection μ S g) :
    IsIntegrableSelection μ (fun ω => L '' S ω) (fun ω => L (g ω)) := by
  refine ⟨L.integrable_comp hg.1, ?_⟩
  filter_upwards [hg.2] with ω hω
  exact ⟨g ω, hω, rfl⟩

/-- For a continuous linear equivalence, transporting a fixed selection
preserves and reflects the integrable-selection property.
@isnad1 id=iff.0h7v.s9.bf68089a3817 from=translated src=- shape=c35f4a08 vocab=ba741cb9
-/
theorem isIntegrableSelection_map_continuousLinearEquiv_iff
    {μ : Measure Ω} {S : Ω → Set E} (e : E ≃L[ℝ] F) (g : Ω → E) :
    IsIntegrableSelection μ (fun ω => e '' S ω) (fun ω => e (g ω)) ↔
      IsIntegrableSelection μ S g := by
  constructor
  · intro hg
    refine ⟨e.integrable_comp_iff.mp hg.1, ?_⟩
    filter_upwards [hg.2] with ω hω
    rcases hω with ⟨z, hz, heq⟩
    have hzg : z = g ω := e.injective heq
    simpa [hzg] using hz
  · intro hg
    exact hg.map_continuousLinearMap e.toContinuousLinearMap

/-! ## Functoriality of the Aumann expectation -/

/-- A continuous linear map sends every point of the Aumann expectation to
the Aumann expectation of the pointwise image correspondence.
@isnad1 id=mem.1h7v.s8.29ded6ae138f from=translated src=- shape=4eb98627 vocab=8a5caf43
-/
theorem map_mem_aumannExpectation_image
    [CompleteSpace E] [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E} (L : E →L[ℝ] F)
    {x : E} (hx : x ∈ aumannExpectation μ S) :
    L x ∈ aumannExpectation μ (fun ω => L '' S ω) := by
  rcases hx with ⟨g, hg, rfl⟩
  refine ⟨fun ω => L (g ω), hg.map_continuousLinearMap L, ?_⟩
  exact L.integral_comp_comm hg.1

/-- Continuous linear images commute with Aumann expectation in the forward
direction.  Equality need not hold for a non-injective or non-surjective map.
@isnad1 id=le.0h6v.s8.92fa5944325e from=translated src=- shape=f2c16590 vocab=80baf188
-/
theorem image_aumannExpectation_subset_aumannExpectation_image
    [CompleteSpace E] [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E} (L : E →L[ℝ] F) :
    L '' aumannExpectation μ S ⊆
      aumannExpectation μ (fun ω => L '' S ω) := by
  rintro _ ⟨x, hx, rfl⟩
  exact map_mem_aumannExpectation_image L hx

/-- The Aumann expectation is equivariant under continuous linear
equivalences.  The inverse inclusion transports a selection back through
`e.symm`, so both strong measurability and integrability are controlled.
@isnad1 id=eq.0h6v.s9.03fec364ecb5 from=translated src=- shape=d99b0f3e vocab=6ba3ee69
-/
theorem image_aumannExpectation_continuousLinearEquiv
    [CompleteSpace E] [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E} (e : E ≃L[ℝ] F) :
    e '' aumannExpectation μ S =
      aumannExpectation μ (fun ω => e '' S ω) := by
  apply Set.Subset.antisymm
  · exact image_aumannExpectation_subset_aumannExpectation_image
      e.toContinuousLinearMap
  · intro y hy
    have hy' : e.symm y ∈
        aumannExpectation μ (fun ω => e.symm '' (e '' S ω)) :=
      map_mem_aumannExpectation_image e.symm.toContinuousLinearMap hy
    have hyS : e.symm y ∈ aumannExpectation μ S := by
      simpa only [e.symm_image_image] using hy'
    exact ⟨e.symm y, hyS, e.apply_symm_apply y⟩

/-! ## Closure and convexification consequences -/

/-- The closure of the Aumann expectation is transported into the closure of
the image Aumann expectation by every continuous linear map.
@isnad1 id=le.0h6v.s8.c34973adc465 from=translated src=- shape=66873ee8 vocab=cdb798b4
-/
theorem image_closure_aumannExpectation_subset
    [CompleteSpace E] [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E} (L : E →L[ℝ] F) :
    L '' closure (aumannExpectation μ S) ⊆
      closure (aumannExpectation μ (fun ω => L '' S ω)) := by
  exact (image_closure_subset_closure_image L.continuous).trans
    (closure_mono (image_aumannExpectation_subset_aumannExpectation_image L))

/-- A continuous linear equivalence commutes with the closed convex hull of a
set.
@isnad1 id=eq.0h4v.s9.2fc54b3b53de from=translated src=- shape=65514cb5 vocab=0929fe40
-/
theorem image_closedConvexHull_continuousLinearEquiv
    (e : E ≃L[ℝ] F) (s : Set E) :
    e '' closedConvexHull ℝ s = closedConvexHull ℝ (e '' s) := by
  have hconv : e '' convexHull ℝ s = convexHull ℝ (e '' s) := by
    simpa only [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.coe_coe] using
      e.toContinuousLinearMap.toLinearMap.image_convexHull s
  rw [closedConvexHull_eq_closure_convexHull, e.image_closure,
    closedConvexHull_eq_closure_convexHull]
  exact congrArg closure hconv

/-- Every continuous linear image of the closed convex hull of an Aumann
expectation lies in the closed convex hull of the image Aumann expectation.
@isnad1 id=le.0h6v.s9.d0a7d76d0cb8 from=translated src=- shape=59a1ad79 vocab=99d135e3
-/
theorem image_closedConvexHull_aumannExpectation_subset
    [CompleteSpace E] [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E} (L : E →L[ℝ] F) :
    L '' closedConvexHull ℝ (aumannExpectation μ S) ⊆
      closedConvexHull ℝ
        (aumannExpectation μ (fun ω => L '' S ω)) := by
  calc
    L '' closedConvexHull ℝ (aumannExpectation μ S) =
        L '' closure (convexHull ℝ (aumannExpectation μ S)) := by
      rw [closedConvexHull_eq_closure_convexHull]
    _ ⊆ closure (L '' convexHull ℝ (aumannExpectation μ S)) :=
      image_closure_subset_closure_image L.continuous
    _ = closure (convexHull ℝ (L '' aumannExpectation μ S)) := by
      have hconv : L '' convexHull ℝ (aumannExpectation μ S) =
          convexHull ℝ (L '' aumannExpectation μ S) := by
        simpa only [ContinuousLinearMap.coe_coe] using
          L.toLinearMap.image_convexHull (aumannExpectation μ S)
      exact congrArg closure hconv
    _ ⊆ closure
        (convexHull ℝ
          (aumannExpectation μ (fun ω => L '' S ω))) :=
      closure_mono (convexHull_mono
        (image_aumannExpectation_subset_aumannExpectation_image L))
    _ = closedConvexHull ℝ
        (aumannExpectation μ (fun ω => L '' S ω)) := by
      rw [closedConvexHull_eq_closure_convexHull]

/-- For a continuous linear equivalence, the closed convex hull of the Aumann
expectation is transported exactly.
@isnad1 id=eq.0h6v.s9.c0e1c88d2a52 from=translated src=- shape=614de102 vocab=16506047
-/
theorem image_closedConvexHull_aumannExpectation_continuousLinearEquiv
    [CompleteSpace E] [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E} (e : E ≃L[ℝ] F) :
    e '' closedConvexHull ℝ (aumannExpectation μ S) =
      closedConvexHull ℝ
        (aumannExpectation μ (fun ω => e '' S ω)) := by
  rw [image_closedConvexHull_continuousLinearEquiv,
    image_aumannExpectation_continuousLinearEquiv]

/-- For a continuous linear equivalence, closure of the Aumann expectation is
transported exactly.
@isnad1 id=eq.0h6v.s9.c06b61e6e4c6 from=translated src=- shape=b4841d11 vocab=cdff8f1e
-/
theorem image_closure_aumannExpectation_continuousLinearEquiv
    [CompleteSpace E] [CompleteSpace F]
    {μ : Measure Ω} {S : Ω → Set E} (e : E ≃L[ℝ] F) :
    e '' closure (aumannExpectation μ S) =
      closure (aumannExpectation μ (fun ω => e '' S ω)) := by
  rw [e.image_closure, image_aumannExpectation_continuousLinearEquiv]

end RandomSetTheory
