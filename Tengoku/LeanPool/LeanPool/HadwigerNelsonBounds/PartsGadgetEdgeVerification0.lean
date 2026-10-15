/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetEmbeddingCore

/-! Generated edge-geometry checks, group 0. -/

@[expose] public section

namespace HadwigerNelsonBounds

/--
@isnad1 id=partsgad.1h1v.s6.f5a7cc9e532e from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase0 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 0) :
    PartsGadgetEdgeCase 0 neighbor := by
  change neighbor ∈ [1, 4, 5] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.b63e2cfdf6c0 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase1 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 1) :
    PartsGadgetEdgeCase 1 neighbor := by
  change neighbor ∈ [0, 2, 5, 6] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.57c9d5a3eda3 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase2 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 2) :
    PartsGadgetEdgeCase 2 neighbor := by
  change neighbor ∈ [1, 3, 6, 7] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.4270d7ec252a from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase3 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 3) :
    PartsGadgetEdgeCase 3 neighbor := by
  change neighbor ∈ [2, 7, 8] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.fe63116a1827 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase4 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 4) :
    PartsGadgetEdgeCase 4 neighbor := by
  change neighbor ∈ [0, 5, 9, 10] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.50abf182ecc5 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase5 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 5) :
    PartsGadgetEdgeCase 5 neighbor := by
  change neighbor ∈ [0, 1, 4, 6, 10, 11, 42] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.c15cdcc4acb5 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase6 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 6) :
    PartsGadgetEdgeCase 6 neighbor := by
  change neighbor ∈ [1, 2, 5, 7, 11, 12] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.c13dbad6d3c4 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase7 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 7) :
    PartsGadgetEdgeCase 7 neighbor := by
  change neighbor ∈ [2, 3, 6, 8, 12, 13, 44] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.2f1a851d3b8e from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase8 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 8) :
    PartsGadgetEdgeCase 8 neighbor := by
  change neighbor ∈ [3, 7, 13, 14] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.b98ebbae2341 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase9 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 9) :
    PartsGadgetEdgeCase 9 neighbor := by
  change neighbor ∈ [4, 10, 15, 16] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.360e34443f01 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase10 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 10) :
    PartsGadgetEdgeCase 10 neighbor := by
  change neighbor ∈ [4, 5, 9, 11, 16, 17] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.fa1d9f821453 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase11 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 11) :
    PartsGadgetEdgeCase 11 neighbor := by
  change neighbor ∈ [5, 6, 10, 12, 17, 18] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.92051ea7c8f0 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase12 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 12) :
    PartsGadgetEdgeCase 12 neighbor := by
  change neighbor ∈ [6, 7, 11, 13, 18, 19] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.c18750fdecd3 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase13 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 13) :
    PartsGadgetEdgeCase 13 neighbor := by
  change neighbor ∈ [7, 8, 12, 14, 19, 20] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.e584de999c7b from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase14 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 14) :
    PartsGadgetEdgeCase 14 neighbor := by
  change neighbor ∈ [8, 13, 20, 21] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.f29fee3893ff from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase15 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 15) :
    PartsGadgetEdgeCase 15 neighbor := by
  change neighbor ∈ [9, 16, 22] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.b5ac51225782 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase16 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 16) :
    PartsGadgetEdgeCase 16 neighbor := by
  change neighbor ∈ [9, 10, 15, 17, 22, 23, 53] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.326461a273b8 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase17 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 17) :
    PartsGadgetEdgeCase 17 neighbor := by
  change neighbor ∈ [10, 11, 16, 18, 23, 24] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.348e3b623099 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase18 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 18) :
    PartsGadgetEdgeCase 18 neighbor := by
  change neighbor ∈ [11, 12, 17, 19, 24, 25, 48, 49, 54, 55, 60, 61] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

end HadwigerNelsonBounds
