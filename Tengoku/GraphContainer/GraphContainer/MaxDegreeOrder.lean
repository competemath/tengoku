/-
Copyright (c) 2026 Graph Container formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Graph Container formalization team
-/
module
public import Tengoku.GraphContainer.GraphContainer.Basic
public import Tengoku.Seed.Analysis.SpecialFunctions.Exp
public import Tengoku.Seed.Combinatorics.SimpleGraph.Clique
public import Tengoku.Seed.Combinatorics.SimpleGraph.DegreeSum
public import Tengoku.Seed.Data.Finset.Powerset
public import Tengoku.Seed.Data.Finset.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Max-degree ordering

This file defines a deterministic max-degree ordering.  At every stage a vertex of maximum degree
in the graph induced by the remaining vertices is chosen.  `Classical.choose` provides stable
tie-breaking without placing an arbitrary order on the public vertex type.

This is work package 1 in `IMPLEMENTATION.md`.
-/

@[expose] public section

open Finset

namespace SimpleGraph.Container

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of neighbors of `v` that lie in `A`.-/
def degreeWithin (A : Finset V) (v : V) : ℕ :=
  #(G.neighborFinset v ∩ A)

/-- A deterministically chosen vertex of maximum degree inside a nonempty active set.-/
noncomputable def maxDegreeVertex (A : Finset V) (hA : A.Nonempty) : V :=
  (Finset.exists_max_image A (degreeWithin G A) hA).choose

/--
@isnad1 id=mem.1h3v.s5.9c06f25ae83b from=translated src=- shape=9a09e3b1 vocab=414ee79b
-/
theorem maxDegreeVertex_mem (A : Finset V) (hA : A.Nonempty) :
    maxDegreeVertex G A hA ∈ A := by
      exact (Finset.exists_max_image A (degreeWithin G A) hA).choose_spec.1

/--
@isnad1 id=le.2h4v.s6.884175fc9a1b from=translated src=- shape=e820c83a vocab=82596c03
-/
theorem degreeWithin_le_maxDegreeVertex (A : Finset V) (hA : A.Nonempty) (v : V)
    (hv : v ∈ A) :
    degreeWithin G A v ≤ degreeWithin G A (maxDegreeVertex G A hA) := by
      exact (Finset.exists_max_image A (degreeWithin G A) hA).choose_spec.2 v hv

/-- The degree within a finset agrees with degree in the corresponding induced graph.
@isnad1 id=eq.0h4v.s8.19eba159beee from=translated src=- shape=5d9b1a62 vocab=496e8cb5
-/
theorem degreeWithin_eq_degree_induce (A : Finset V) (v : A) :
    degreeWithin G A v = (G.induce (A : Set V)).degree v := by
  calc
    degreeWithin G A v = #(G.neighborFinset v ∩ A) := rfl
    _ = #(((G.induce (A : Set V)).neighborFinset v).map (.subtype (· ∈ (A : Set V)))) := by
      congr 1
      ext x
      simp
    _ = (G.induce (A : Set V)).degree v := Finset.card_map _

/-- Iteratively remove a maximum-degree vertex.-/
noncomputable def maxDegreeOrder (A : Finset V) : List V :=
  if hA : A.Nonempty then
    let v := maxDegreeVertex G A hA
    v :: maxDegreeOrder (A.erase v)
  else
    []
termination_by A.card
decreasing_by
  exact Finset.card_erase_lt_of_mem (maxDegreeVertex_mem G A hA)

/--
@isnad1 id=eq.0h2v.s5.eadf7ec3ac75 from=translated src=- shape=30a8aef0 vocab=895da820
-/
theorem maxDegreeOrder_empty : maxDegreeOrder G ∅ = [] := by
  rw [maxDegreeOrder]
  exact dite_eq_right Finset.not_nonempty_empty

/--
@isnad1 id=iff.0h3v.s5.c1a8049122b2 from=translated src=- shape=63237b4e vocab=895da820
-/
theorem maxDegreeOrder_eq_nil_iff (A : Finset V) :
    maxDegreeOrder G A = [] ↔ A = ∅ := by
    constructor
    · intro h
      by_contra hA
      have hA' : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
      rw [maxDegreeOrder, dite_eq_left hA'] at h
      change maxDegreeVertex G A hA' ::
        maxDegreeOrder G (A.erase (maxDegreeVertex G A hA')) = [] at h
      exact (List.cons_ne_nil _ _) h
    · rintro rfl
      exact maxDegreeOrder_empty G

private theorem maxDegreeOrder_nodup_and_toFinset (A : Finset V) :
    (maxDegreeOrder G A).Nodup ∧
      (maxDegreeOrder G A).toFinset = A := by
  classical
  refine Finset.strongInductionOn A (fun A ih => ?_)
  by_cases hA : A.Nonempty
  · rw [maxDegreeOrder, dite_eq_left hA]
    let v := maxDegreeVertex G A hA
    have hv : v ∈ A := maxDegreeVertex_mem G A hA
    have htail := ih (A.erase v) (Finset.erase_ssubset hv)
    constructor
    · apply List.nodup_cons.mpr
      constructor
      · intro hmem
        have hmem' : v ∈ (maxDegreeOrder G (A.erase v)).toFinset :=
          List.mem_toFinset.mpr hmem
        rw [htail.2] at hmem'
        exact (Finset.mem_erase.mp hmem').1 rfl
      · exact htail.1
    · rw [List.toFinset_cons, htail.2]
      exact Finset.insert_erase hv
  · rw [maxDegreeOrder, dite_eq_right hA, List.toFinset_nil]
    exact ⟨List.nodup_nil, (not_nonempty_iff_eq_empty.mp hA).symm⟩

/--
@isnad1 id=nodup.0h3v.s4.f3806ab6c9fb from=translated src=- shape=d0ca0649 vocab=06140100
-/
theorem maxDegreeOrder_nodup (A : Finset V) :
    (maxDegreeOrder G A).Nodup := by
  exact (maxDegreeOrder_nodup_and_toFinset G A).1

/--
@isnad1 id=eq.0h3v.s5.3f033ae9c139 from=translated src=- shape=0e2b9bee vocab=92f81f72
-/
@[simp]
theorem maxDegreeOrder_toFinset (A : Finset V) :
    (maxDegreeOrder G A).toFinset = A := by
  exact (maxDegreeOrder_nodup_and_toFinset G A).2

/--
@isnad1 id=eq.0h3v.s5.21c3b18d2421 from=translated src=- shape=5ef06681 vocab=00580a77
-/
@[simp]
theorem length_maxDegreeOrder (A : Finset V) :
    (maxDegreeOrder G A).length = #A := by
  have h := maxDegreeOrder_nodup_and_toFinset G A
  calc
    (maxDegreeOrder G A).length = #(maxDegreeOrder G A).toFinset :=
      (List.toFinset_card_of_nodup h.1).symm
    _ = #A := by rw [h.2]

/-- Every vertex is maximal when it is reached in the max-degree ordering.
@isnad1 id=le.2h7v.s6.583383a8144f from=translated src=- shape=83339166 vocab=2b9bc374
-/
theorem degreeWithin_le_of_maxDegreeOrder_eq_append_cons
    (A : Finset V) {before suffix : List V} {v w : V}
    (horder : maxDegreeOrder G A = before ++ v :: suffix)
    (hw : w ∈ (v :: suffix).toFinset) :
    degreeWithin G (v :: suffix).toFinset w ≤
      degreeWithin G (v :: suffix).toFinset v := by
  induction before generalizing A with
  | nil =>
    have hA : A.Nonempty := by
      by_contra hA
      have hzero : A = ∅ := not_nonempty_iff_eq_empty.mp hA
      subst A
      rw [maxDegreeOrder_empty] at horder
      simp at horder
    have horder' : maxDegreeOrder G A = v :: suffix := by
      simpa only [List.nil_append] using horder
    have hset : (v :: suffix).toFinset = A := by
      rw [← horder']
      exact (maxDegreeOrder_nodup_and_toFinset G A).2
    rw [maxDegreeOrder, dite_eq_left hA] at horder'
    dsimp only at horder'
    injection horder' with hhead htail
    have hwA : w ∈ A := by
      rw [← hset]
      exact hw
    have hmax := degreeWithin_le_maxDegreeVertex G A hA w hwA
    simpa only [hset, hhead] using hmax
  | cons a before ih =>
    have hA : A.Nonempty := by
      by_contra hA
      have hzero : A = ∅ := not_nonempty_iff_eq_empty.mp hA
      subst A
      rw [maxDegreeOrder_empty] at horder
      simp at horder
    have horder' : maxDegreeOrder G A = a :: (before ++ v :: suffix) := by
      simpa only [List.cons_append] using horder
    rw [maxDegreeOrder, dite_eq_left hA] at horder'
    dsimp only at horder'
    injection horder' with hhead htail
    exact ih (A.erase (maxDegreeVertex G A hA)) htail

end SimpleGraph.Container
