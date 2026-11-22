/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Tengoku.Seed.MeasureTheory.Function.L1Space.Integrable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LeanPool.RlTheoryInLean.MeasureTheory.Function.L1Space.Integrable
-/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
open Filter

namespace MeasureTheory
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/--
@isnad1 id=integrab.2h5v.s6.ea862651c492 from=translated src=- shape=5b1db38d vocab=9f2e3be3
-/
lemma integrable_of_norm_le {α : Type*} {β : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [IsFiniteMeasure μ] [NormedAddCommGroup β] {f : α → β}
  (hm : AEStronglyMeasurable f μ) (hbdd : ∃ C, ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C)
  : Integrable f μ := by
  obtain ⟨C, hC⟩ := hbdd
  apply integrable_of_norm_sub_le (f₀ := 0) (g := fun ω => C) hm (integrable_const _)
    (integrable_const _)
  exact hC.mono fun ω hω => by simp [hω]

/--
@isnad1 id=integrab.1h6v.s6.94a1b43c7f50 from=translated src=- shape=ed770824 vocab=b2976bd2
-/
lemma Integrable.finset_sum
  {α ι : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [IsFiniteMeasure μ] {s : Finset ι} {f : ι → α → ℝ}
  (hf : ∀ i ∈ s, Integrable (f i) μ) :
  Integrable (fun ω => ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_all

end MeasureTheory
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
