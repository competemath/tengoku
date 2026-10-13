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

/--
@isnad1 id=iff.0h5v.s7.59ca21e2be6b from=translated src=- shape=5b66f200 vocab=3f99a67b
-/
theorem mem_region (C : (B.induce {v | v ∈ U}).ConnectedComponent) {v : V} :
    v ∈ region B U C ↔ ∃ h : v ∈ U, (⟨v, h⟩ : {v // v ∈ U}) ∈ C.supp := by
  constructor
  · intro hv
    obtain ⟨w, member, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨w.property, Set.mem_toFinset.mp member⟩
  · rintro ⟨h, member⟩
    exact Finset.mem_image.mpr ⟨⟨v, h⟩, Set.mem_toFinset.mpr member, rfl⟩

/--
@isnad1 id=le.0h4v.s6.1557bc97c309 from=translated src=- shape=253cc4a3 vocab=42afa54f
-/
theorem region_subset (C : (B.induce {v | v ∈ U}).ConnectedComponent) : region B U C ⊆ U :=
  fun _ hv => ((mem_region B U C).mp hv).choose

/--
@isnad1 id=connecte.0h4v.s6.ac31adb3b5ae from=translated src=- shape=900044d5 vocab=7a7efbac
-/
theorem region_connected (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    (B.induce {v | v ∈ region B U C}).Connected := by
  let hom : C.toSimpleGraph →g B.induce {v | v ∈ region B U C} :=
    ⟨fun v => ⟨v.val.val, (mem_region B U C).mpr ⟨v.val.property, v.property⟩⟩, fun h => h⟩
  apply C.connected_toSimpleGraph.map hom
  intro v
  obtain ⟨hv, member⟩ := (mem_region B U C).mp v.property
  exact ⟨⟨⟨v.val, hv⟩, member⟩, rfl⟩

/--
@isnad1 id=iff.0h4v.s6.a453e9f1a4a3 from=translated src=- shape=630bf8b9 vocab=66e119c0
-/
theorem exists_mem_region {v : V} :
    (∃ C : (B.induce {v | v ∈ U}).ConnectedComponent, v ∈ region B U C) ↔ v ∈ U := by
  constructor
  · rintro ⟨C, member⟩
    exact region_subset B U C member
  · intro hv
    refine ⟨(B.induce {v | v ∈ U}).connectedComponentMk ⟨v, hv⟩,
      (mem_region B U _).mpr ⟨hv, ?_⟩⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl

/--
@isnad1 id=pairwise.0h3v.s7.137bea61e464 from=translated src=- shape=083ab69b vocab=a7d099e2
-/
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
