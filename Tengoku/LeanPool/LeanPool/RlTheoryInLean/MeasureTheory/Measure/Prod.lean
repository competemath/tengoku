/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Tengoku

/-!
# LeanPool.RlTheoryInLean.MeasureTheory.Measure.Prod
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure  ProbabilityTheory Finset NNReal ENNReal Preorder Filter

namespace MeasureTheory.Measure

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/--
@isnad1 id=eq.1h5v.s6.9e68cdaa1ae7 from=translated src=- shape=6ee2d433 vocab=c02b5f43
-/
lemma prod_preimage_snd
  (μ : Measure α) (ν : Measure β) (hν : SFinite ν) (A : Set β) :
  (μ.prod ν) (Prod.snd ⁻¹' A) = μ Set.univ * ν A := by
  rw [show Prod.snd ⁻¹' A = (Set.univ : Set α) ×ˢ A from by ext ⟨x, y⟩; simp,
      Measure.prod_prod]

/--
@isnad1 id=eq.1h5v.s6.3fdf8066bb7e from=translated src=- shape=9d674649 vocab=63670938
-/
lemma prod_preimage_fst
  (μ : Measure α) (ν : Measure β) (hν : SFinite ν) (A : Set α) :
  (μ.prod ν) (Prod.fst ⁻¹' A) = μ A * ν Set.univ := by
  rw [show Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set β) from by ext ⟨x, y⟩; simp,
      Measure.prod_prod]

/--
@isnad1 id=eq.2h7v.s6.6cce01df286a from=translated src=- shape=ca02c421 vocab=728ebaa4
-/
lemma map_prodMk_dirac
  {X : α → β} {Y : α → γ} {μ : Measure α}
  {C : β} (hC : ∀ᵐ a ∂μ, X a = C)
  (hY : Measurable Y) [SFinite (Measure.map Y μ)] :
  (Measure.map (fun a ↦ (X a, Y a)) μ) =
    (Measure.dirac C).prod (Measure.map Y μ) := by
  have h₁ : Measure.map (fun a ↦ (X a, Y a)) μ = Measure.map (fun a ↦ (C, Y a)) μ := by
    apply Measure.map_congr
    filter_upwards [hC] with x hx
    rw [hx]
  rw [h₁, dirac_prod, Measure.map_map measurable_prodMk_left hY]
  rfl

end MeasureTheory.Measure
