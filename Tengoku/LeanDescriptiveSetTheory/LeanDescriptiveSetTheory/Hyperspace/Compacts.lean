/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic
import Tengoku.Seed.Topology.MetricSpace.Closeds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compact hyperspaces

This module is a thin measurable-facing layer over mathlib's Vietoris topologies on
`TopologicalSpace.Compacts` and `TopologicalSpace.NonemptyCompacts`.  It introduces no topology or
global measurable-space instance.
-/

open MeasurableSpace Set TopologicalSpace Topology

universe u

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X]

/-- The Borel measurable space of mathlib's Vietoris compact hyperspace.-/
abbrev compactsBorelMeasurableSpace : MeasurableSpace (Compacts X) :=
  borel (Compacts X)

/-- The Borel measurable space of mathlib's nonempty Vietoris compact hyperspace.-/
abbrev nonemptyCompactsBorelMeasurableSpace : MeasurableSpace (NonemptyCompacts X) :=
  borel (NonemptyCompacts X)

/-- Compact sets meeting an open set form a Vietoris-open set.
@isnad1 id=isopen.1h2v.s5.1c89cb74cc21 from=translated src=- shape=4f1a4133 vocab=2baa0da2
-/
theorem isOpen_compactsHit {U : Set X} (hU : IsOpen U) :
    IsOpen {K : Compacts X | ((K : Set X) ∩ U).Nonempty} :=
  Compacts.isOpen_inter_nonempty_of_isOpen hU

/-- Nonempty compact sets meeting an open set form a Vietoris-open set.
@isnad1 id=isopen.1h2v.s5.9fe0eb42ff2b from=translated src=- shape=4f1a4133 vocab=d5b759f8
-/
theorem isOpen_nonemptyCompactsHit {U : Set X} (hU : IsOpen U) :
    IsOpen {K : NonemptyCompacts X | ((K : Set X) ∩ U).Nonempty} :=
  NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU

/-- Open-hit sets are measurable in the Borel space of the compact Vietoris topology.
@isnad1 id=measurab.1h2v.s5.deda42b0b70a from=translated src=- shape=35b76f56 vocab=69acf9b4
-/
theorem measurableSet_compactsHit {U : Set X} (hU : IsOpen U) :
    @MeasurableSet (Compacts X) compactsBorelMeasurableSpace
      {K | ((K : Set X) ∩ U).Nonempty} :=
  measurableSet_generateFrom (isOpen_compactsHit hU)

/-- Open-hit sets are measurable in the Borel space of the nonempty compact Vietoris topology.
@isnad1 id=measurab.1h2v.s5.6ecec68ceaa6 from=translated src=- shape=35b76f56 vocab=c4328d0f
-/
theorem measurableSet_nonemptyCompactsHit {U : Set X} (hU : IsOpen U) :
    @MeasurableSet (NonemptyCompacts X) nonemptyCompactsBorelMeasurableSpace
      {K | ((K : Set X) ∩ U).Nonempty} :=
  measurableSet_generateFrom (isOpen_nonemptyCompactsHit hU)

/-- Mathlib's nonempty Vietoris compact hyperspace is Polish over a Polish base space.

This is a named theorem rather than a global instance so that the project does not duplicate or
change mathlib's instance surface.
@isnad1 id=polishsp.0h1v.s4.966a175dcbd5 from=translated src=- shape=d96e9922 vocab=c11b5186
-/
theorem polishSpace_nonemptyCompacts_vietoris [PolishSpace X] :
    PolishSpace (NonemptyCompacts X) := by
  letI := upgradeIsCompletelyMetrizable X
  haveI : IsCompletelyMetrizableSpace (Closeds X) := by infer_instance
  haveI : IsCompletelyMetrizableSpace (NonemptyCompacts X) :=
    NonemptyCompacts.isClosedEmbedding_toCloseds.IsCompletelyMetrizableSpace
  infer_instance

private theorem isOpenEmbedding_botCompacts :
    IsOpenEmbedding (fun _ : PUnit => (⊥ : Compacts X)) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_const
    (fun _ _ _ => Subsingleton.elim _ _)
  intro s hs
  by_cases h : s.Nonempty
  · convert Compacts.isClopen_singleton_bot.isOpen using 1
    ext K
    simp [h]
  · rw [not_nonempty_iff_eq_empty.mp h]
    simp

/-- Mathlib's Vietoris compact hyperspace, including the empty compact set, is Polish over a
Polish base space.

The proof separates the isolated empty compact set from the nonempty compact hyperspace. This is a
named theorem rather than a global instance.
@isnad1 id=polishsp.0h1v.s4.3921a8d27250 from=translated src=- shape=d96e9922 vocab=fe80f703
-/
theorem polishSpace_compacts_vietoris [PolishSpace X] : PolishSpace (Compacts X) := by
  letI : PolishSpace (NonemptyCompacts X) := polishSpace_nonemptyCompacts_vietoris
  let f : PUnit ⊕ NonemptyCompacts X → Compacts X :=
    Sum.elim (fun _ => ⊥) NonemptyCompacts.toCompacts
  have hf : IsOpenEmbedding f := by
    apply isOpenEmbedding_botCompacts.sumElim NonemptyCompacts.isOpenEmbedding_toCompacts
    intro a b hab
    rcases a with a | K <;> rcases b with b | L
    · exact congrArg Sum.inl (Subsingleton.elim a b)
    · have hsets : (∅ : Set X) = (L : Set X) := by
        simpa using congrArg (fun C : Compacts X => (C : Set X)) hab
      exact (L.nonempty.ne_empty hsets.symm).elim
    · have hsets : (K : Set X) = ∅ := by
        simpa using congrArg (fun C : Compacts X => (C : Set X)) hab
      exact (K.nonempty.ne_empty hsets).elim
    · exact congrArg Sum.inr (NonemptyCompacts.toCompacts_injective hab)
  have hsurj : Function.Surjective f := by
    intro K
    by_cases hK : K = ⊥
    · exact ⟨Sum.inl PUnit.unit, hK.symm⟩
    · exact ⟨Sum.inr ⟨K, Compacts.coe_nonempty.mpr hK⟩, rfl⟩
  exact (hf.isEmbedding.toHomeomorphOfSurjective hsurj).symm.isClosedEmbedding.polishSpace

/-- For a Polish base space, mathlib's compact Vietoris hyperspace with its Borel structure is
standard Borel.
@isnad1 id=standard.0h1v.s4.8fe41912a156 from=translated src=- shape=9499e9bc vocab=4dd3e08d
-/
theorem standardBorelSpace_compacts [PolishSpace X] :
    @StandardBorelSpace (Compacts X) compactsBorelMeasurableSpace := by
  letI : PolishSpace (Compacts X) := polishSpace_compacts_vietoris
  letI : MeasurableSpace (Compacts X) := compactsBorelMeasurableSpace
  letI : BorelSpace (Compacts X) := ⟨rfl⟩
  infer_instance

/-- For a Polish base space, the nonempty compact Vietoris hyperspace with its Borel structure is
standard Borel.
@isnad1 id=standard.0h1v.s4.c77ba1332385 from=translated src=- shape=9499e9bc vocab=9f7c0bad
-/
theorem standardBorelSpace_nonemptyCompacts [PolishSpace X] :
    @StandardBorelSpace (NonemptyCompacts X) nonemptyCompactsBorelMeasurableSpace := by
  letI : PolishSpace (NonemptyCompacts X) := polishSpace_nonemptyCompacts_vietoris
  letI : MeasurableSpace (NonemptyCompacts X) := nonemptyCompactsBorelMeasurableSpace
  letI : BorelSpace (NonemptyCompacts X) := ⟨rfl⟩
  infer_instance

end DescriptiveSetTheory
