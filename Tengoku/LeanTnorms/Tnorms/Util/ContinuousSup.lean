/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
TODOs:
  * General proof cleanup
  * Some of these been added to Mathlib. (Look at {Left,Right}OrdContinuous)
  * Can we weaken the typeclass assumptions?
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
variable {α β : Type*}
    [CompleteLinearOrder α] [CompleteLattice β]
    [TopologicalSpace α] [TopologicalSpace β]
    [OrderTopology α] [OrderTopology β]
    [FirstCountableTopology α]

/--
@isnad1 id=eq.3h4v.s6.587177dfb036 from=translated src=- shape=75ed3691 vocab=ef92e9cb
-/
lemma _root_.Tengoku.LeanTnorms.is_sSupHom_of_continuous_mono' {f : α → β} (h : Continuous f) (hm : Monotone f)
    (S : Set α) (hS : S.Nonempty) : sSup (f '' S) = f (sSup S) := by
  suffices ¬ sSup (f '' S) < f (sSup S) by
    have hfs : sSup (f '' S) ≤ f (sSup S) := by
      refine sSup_le ?_
      simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a ha
      refine hm ?_
      exact le_sSup ha
    contrapose! this
    exact lt_of_le_of_ne hfs this
  by_contra!
  obtain ⟨u, hum, hu, huS⟩ := exists_seq_tendsto_sSup hS (OrderTop.bddAbove S)
  apply Continuous.seqContinuous at h
  specialize h hu
  contrapose! h; clear h
  simp [Filter.tendsto_iff_forall_eventually_mem]
  use Set.Ioi (sSup (f '' S))
  constructor
  · exact IsOpen.mem_nhds (isOpen_Ioi' (sSup (f '' S))) (by grind)
  · intro n
    use n
    simp only [le_refl, Set.mem_Ioi, true_and]
    suffices f (u n) ≤ sSup (f '' S) by grind
    exact le_sSup (by grind)

/--
@isnad1 id=eq.3h4v.s7.f8530744dffe from=translated src=- shape=2a635965 vocab=6fe5675d
-/
lemma _root_.Tengoku.LeanTnorms.is_sSupHom_of_continuous_mono {f : α → β} (h : Continuous f) (hm : Monotone f)
    (hb : f ⊥ = ⊥) (S : Set α) : sSup (f '' S) = f (sSup S) := by
  by_cases! hS : ¬S.Nonempty
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    simp [hS, hb]
  exact is_sSupHom_of_continuous_mono' h hm S hS
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
