/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.DegreeReduction
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.RankCount

/-!
# A cloud, by counting

Degree reduction rotates inside a cloud through the cloud's enumeration: the
half-edge it starts from is located by `List.idxOf`, and the one it lands on is
read off by position. Neither operation is available to an algorithm, which can
only count. This module replaces both by counts of half-edge numbers.

The cloud is enumerated in order of those numbers, so a half-edge's position is
the number of smaller numbers in the cloud, and the half-edge at a position is
the one whose number has that many smaller numbers below it.

## Main definitions

- `Complexity.ConstraintGraph.cloudCodes` — the numbers of a cloud's half-edges

## Main results

- `Complexity.ConstraintGraph.idxOf_cloudList` — the position is a count
- `Complexity.ConstraintGraph.halfCode_getElem_cloudList` — and the entry at a
  position is named by the count that reaches it
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

variable {α : Type} (G : ConstraintGraph α)

/-- The numbers of the half-edges attached to a vertex. -/
noncomputable def cloudCodes (v : Fin G.numVerts) : Finset ℕ := (G.cloud v).image G.halfCode

/--
@isnad1 id=iff.0h4v.s5.cb2e64918dc8 from=translated src=- shape=aa0f474c vocab=18c6ad64
-/
@[simp] theorem mem_cloudCodes {v : Fin G.numVerts} {c : ℕ} :
    c ∈ G.cloudCodes v ↔ ∃ p, G.owner p = v ∧ G.halfCode p = c := by
  rw [cloudCodes, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (G.mem_cloud).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (G.mem_cloud).mpr hp, rfl⟩

/--
@isnad1 id=eq.0h3v.s4.7d6d016cdc17 from=translated src=- shape=96804f77 vocab=897cea3c
-/
@[simp] theorem card_cloudCodes (v : Fin G.numVerts) :
    (G.cloudCodes v).card = (G.cloud v).card :=
  Finset.card_image_of_injective _ G.halfCode_injective

/--
@isnad1 id=eq.0h3v.s4.c43a872bbfae from=translated src=- shape=7eb71bb5 vocab=d06a47d9
-/
@[simp] theorem length_cloudList (v : Fin G.numVerts) :
    (G.cloudList v).length = (G.cloud v).card := Finset.length_sort _

/-- Counting the smaller numbers of a cloud is counting its smaller
half-edges.
@isnad1 id=eq.0h4v.s5.a6098010a117 from=translated src=- shape=1900e9f0 vocab=f7aca65a
-/
theorem countBelow_cloudCodes (v : Fin G.numVerts) (c : ℕ) :
    countBelow (G.cloudCodes v) c
      = ((G.cloud v).filter fun q => G.halfCode q < c).card := by
  classical
  rw [countBelow, cloudCodes, Finset.filter_image]
  exact Finset.card_image_of_injective _ G.halfCode_injective

/-- **A half-edge's position in its cloud is a count.**
@isnad1 id=eq.1h4v.s5.53301c846b70 from=translated src=- shape=6b1a6307 vocab=deef3640
-/
theorem idxOf_cloudList {v : Fin G.numVerts} {p : G.HalfEdge} (hp : G.owner p = v) :
    (G.cloudList v).idxOf p = countBelow (G.cloudCodes v) (G.halfCode p) := by
  have hmem : p ∈ G.cloudList v := (G.mem_cloudList).mpr ((G.mem_cloud).mpr hp)
  have hinj : ∀ x ∈ G.cloudList v, ∀ y ∈ G.cloudList v, G.halfCode x = G.halfCode y → x = y :=
    fun x _ y _ h => G.halfCode_injective h
  have h1 : (G.cloudList v).idxOf p
      = (G.cloudList v).countP (fun q => decide (G.halfCode q < G.halfCode p)) :=
    idxOf_eq_countP (G.pairwise_cloudList v) hinj hmem
  rw [h1, countBelow_cloudCodes, List.countP_eq_length_filter]
  have hnd : ((G.cloudList v).filter fun q => decide (G.halfCode q < G.halfCode p)).Nodup :=
    (G.nodup_cloudList v).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext q
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, mem_cloudList,
    decide_eq_true_eq]

/--
@isnad1 id=eq.0h3v.s4.cc891efbbd07 from=translated src=- shape=c50d5e30 vocab=dce941de
-/
theorem card_cloudCodes_eq_length (v : Fin G.numVerts) :
    (G.cloudCodes v).card = (G.cloudList v).length := by
  rw [card_cloudCodes, length_cloudList]

/-- **The half-edge at a position is named by the count that reaches it.**
@isnad1 id=eq.1h4v.s7.549641a44804 from=translated src=- shape=491a4464 vocab=dbe0d497
-/
theorem halfCode_getElem_cloudList (v : Fin G.numVerts) (k : ℕ)
    (hk : k < (G.cloudList v).length) :
    (G.cloudCodes v).orderEmbOfFin (G.card_cloudCodes_eq_length v) ⟨k, hk⟩
      = G.halfCode ((G.cloudList v)[k]) := by
  classical
  have hmem : (G.cloudList v)[k] ∈ G.cloudList v := List.getElem_mem hk
  have howner : G.owner ((G.cloudList v)[k]) = v :=
    (G.mem_cloud).mp ((G.mem_cloudList).mp hmem)
  have hcode : G.halfCode ((G.cloudList v)[k]) ∈ G.cloudCodes v :=
    (G.mem_cloudCodes).mpr ⟨_, howner, rfl⟩
  have hidx : (G.cloudList v).idxOf ((G.cloudList v)[k]) = k :=
    (G.nodup_cloudList v).idxOf_getElem _ hk
  refine orderEmbOfFin_eq_of_countBelow (G.card_cloudCodes_eq_length v) _ hcode ?_
  rw [← G.idxOf_cloudList howner, hidx]

end ConstraintGraph

end Complexity
