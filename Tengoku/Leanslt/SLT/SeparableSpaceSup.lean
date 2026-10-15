/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Sho sonoda, Yuma Mizuno
-/
import Tengoku

universe u v

open TopologicalSpace

/--
@isnad1 id=le.2h3v.s6.5c6e29b868d0 from=translated src=- shape=bcf2857b vocab=e6507836
-/
lemma closure_mem_le_sSup {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E] [OrderClosedTopology E]
  {s : Set E} (hs' : BddAbove s) {b : E} (hb : b ∈ closure s) :
  b ≤ sSup s := by
    have : s ⊆ Set.Iic (sSup s) := by
      intro x hx
      exact le_csSup hs' hx
    have : closure s ⊆ Set.Iic (sSup s) := by
      apply closure_minimal this isClosed_Iic
    exact this hb

/--
@isnad1 id=eq.2h2v.s6.e1291463315a from=translated src=- shape=788743d1 vocab=64c7f5e8
-/
lemma sSup_eq_closure_sSup {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E] [OrderClosedTopology E]
  {s : Set E} (hs : s.Nonempty) (hs' : BddAbove s) :
  sSup s = sSup (closure s) := by
  have h' : (BddAbove (closure s)) := by
    use sSup s
    intro b hb
    exact closure_mem_le_sSup hs' hb
  apply le_antisymm
  · apply csSup_le_csSup h' hs
    exact subset_closure
  · apply csSup_le (by aesop)
    exact fun b hb ↦ closure_mem_le_sSup hs' hb

/--
@isnad1 id=eq.1h3v.s6.7cfc7947ce9a from=translated src=- shape=bde5a292 vocab=f167afc4
-/
lemma closure_range_eq_closure_denseSeq {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
  {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E] [OrderClosedTopology E]
  {f : X → E} (hf : Continuous f) :
  closure (Set.range f) = closure (Set.range (f ∘ denseSeq X)) := by
  rw [Set.range_comp f (denseSeq X)]
  apply Set.Subset.antisymm
  · have : Dense (Set.range (denseSeq X)) := denseRange_denseSeq X
    have := hf.range_subset_closure_image_dense this
    exact closure_minimal this isClosed_closure
  · apply closure_mono
    exact Set.image_subset_range f (Set.range (denseSeq X))

/--
@isnad1 id=eq.2h3v.s6.a33e8d64b31f from=translated src=- shape=b100b7d2 vocab=297c905b
-/
theorem separableSpaceSup_eq {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
  {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E] [OrderClosedTopology E]
  {f : X → E} (hf : Continuous f) (hf' : BddAbove (Set.range f)) :
  ⨆ x : X, f x = ⨆ i : Nat, f (denseSeq X i) := by
  calc
    _ = sSup (closure (Set.range f)) := by
      exact sSup_eq_closure_sSup (Set.range_nonempty f) hf'
    _ = sSup (closure (Set.range (f ∘ denseSeq X))) := by
      rw [closure_range_eq_closure_denseSeq hf]
    _ = sSup (Set.range (f ∘ denseSeq X)) := by
      have hf'' : BddAbove (Set.range (f ∘ denseSeq X)) := by
        rw [Set.range_comp f (denseSeq X)]
        have := Set.image_subset_range f (Set.range (denseSeq X))
        exact BddAbove.mono this hf'
      exact (sSup_eq_closure_sSup (Set.range_nonempty (f ∘ denseSeq X)) hf'').symm

/--
@isnad1 id=eq.1h2v.s5.fc1c9435e611 from=translated src=- shape=36f0e889 vocab=66d24d4a
-/
theorem separableSpaceSup_eq_real {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
  {f : X → ℝ} (hf : Continuous f) :
  ⨆ x : X, f x = ⨆ i : Nat, f (denseSeq X i) := by
  if bdd : BddAbove (Set.range f) then
    exact separableSpaceSup_eq hf bdd
  else
    have : ¬ (BddAbove (Set.range (f ∘ (denseSeq X)))) := by
      intro h
      have : BddAbove (closure (Set.range (f ∘ (denseSeq X)))) := bddAbove_closure.mpr h
      rw [←closure_range_eq_closure_denseSeq hf] at this
      exact bdd <| bddAbove_closure.mp this
    calc
      _ = 0 := Real.iSup_of_not_bddAbove bdd
      _ = _ := (Real.iSup_of_not_bddAbove this).symm
