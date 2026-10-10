/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.SpanningPath
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Internal

/-!
# Constructing the degree-two regions

Induced connected components partition the eligible vertices, with no
black edges between distinct regions. Their boundary cuts are therefore
pairwise disjoint. Degree at most two gives a spanning path and at most
two boundary edges; degree exactly two makes the boundary size even.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V : Type} (B : SimpleGraph V) (U : Finset V)

theorem mem_region (C : (B.induce {v | v ∈ U}).ConnectedComponent) {v : V} :
    v ∈ region B U C ↔ ∃ h : v ∈ U, (⟨v, h⟩ : {v // v ∈ U}) ∈ C.supp := by
  constructor
  · intro hv
    obtain ⟨w, member, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨w.property, Set.mem_toFinset.mp member⟩
  · rintro ⟨h, member⟩
    exact Finset.mem_image.mpr ⟨⟨v, h⟩, Set.mem_toFinset.mpr member, rfl⟩

theorem region_subset (C : (B.induce {v | v ∈ U}).ConnectedComponent) : region B U C ⊆ U :=
  fun _ hv => ((mem_region B U C).mp hv).choose

theorem region_connected (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    (B.induce {v | v ∈ region B U C}).Connected := by
  let hom : C.toSimpleGraph →g B.induce {v | v ∈ region B U C} :=
    ⟨fun v => ⟨v.val.val, (mem_region B U C).mpr ⟨v.val.property, v.property⟩⟩, fun h => h⟩
  apply C.connected_toSimpleGraph.map hom
  intro v
  obtain ⟨hv, member⟩ := (mem_region B U C).mp v.property
  exact ⟨⟨⟨v.val, hv⟩, member⟩, rfl⟩

theorem exists_mem_region {v : V} :
    (∃ C : (B.induce {v | v ∈ U}).ConnectedComponent, v ∈ region B U C) ↔ v ∈ U := by
  constructor
  · rintro ⟨C, member⟩
    exact region_subset B U C member
  · intro hv
    refine ⟨(B.induce {v | v ∈ U}).connectedComponentMk ⟨v, hv⟩,
      (mem_region B U _).mpr ⟨hv, ?_⟩⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl

theorem region_disjoint : Pairwise
    (fun C D : (B.induce {v | v ∈ U}).ConnectedComponent =>
      Disjoint (region B U C) (region B U D)) := by
  intro C D different
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨_, hc⟩ := (mem_region B U C).mp hv
  obtain ⟨_, hd⟩ := (mem_region B U D).mp hw
  exact different (SimpleGraph.ConnectedComponent.eq_of_common_vertex hc hd)

variable [Fintype V]

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal
