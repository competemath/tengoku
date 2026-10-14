/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetEmbeddingCore

/-! Generated edge-geometry checks, group 1. -/

@[expose] public section

namespace HadwigerNelsonBounds

/--
@isnad1 id=partsgad.1h1v.s6.18f77097a651 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase19 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 19) :
    PartsGadgetEdgeCase 19 neighbor := by
  change neighbor ∈ [12, 13, 18, 20, 25, 26] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.6a0412fc8716 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase20 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 20) :
    PartsGadgetEdgeCase 20 neighbor := by
  change neighbor ∈ [13, 14, 19, 21, 26, 27, 56] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.1acb87926576 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase21 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 21) :
    PartsGadgetEdgeCase 21 neighbor := by
  change neighbor ∈ [14, 20, 27] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.049d22b2f346 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase22 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 22) :
    PartsGadgetEdgeCase 22 neighbor := by
  change neighbor ∈ [15, 16, 23, 28] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.0a7e7ebe9245 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase23 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 23) :
    PartsGadgetEdgeCase 23 neighbor := by
  change neighbor ∈ [16, 17, 22, 24, 28, 29] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.e0059674a6d8 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase24 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 24) :
    PartsGadgetEdgeCase 24 neighbor := by
  change neighbor ∈ [17, 18, 23, 25, 29, 30] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.4c904eb34058 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase25 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 25) :
    PartsGadgetEdgeCase 25 neighbor := by
  change neighbor ∈ [18, 19, 24, 26, 30, 31] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.a425fbcfde6e from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase26 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 26) :
    PartsGadgetEdgeCase 26 neighbor := by
  change neighbor ∈ [19, 20, 25, 27, 31, 32] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.8ec7f69d3530 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase27 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 27) :
    PartsGadgetEdgeCase 27 neighbor := by
  change neighbor ∈ [20, 21, 26, 32] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.5a874230d487 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase28 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 28) :
    PartsGadgetEdgeCase 28 neighbor := by
  change neighbor ∈ [22, 23, 29, 33] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.bc579ba98f71 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase29 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 29) :
    PartsGadgetEdgeCase 29 neighbor := by
  change neighbor ∈ [23, 24, 28, 30, 33, 34, 65] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.5fc5966787ff from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase30 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 30) :
    PartsGadgetEdgeCase 30 neighbor := by
  change neighbor ∈ [24, 25, 29, 31, 34, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.0219bde431cf from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase31 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 31) :
    PartsGadgetEdgeCase 31 neighbor := by
  change neighbor ∈ [25, 26, 30, 32, 35, 36, 67] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.ee72a78b9cae from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase32 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 32) :
    PartsGadgetEdgeCase 32 neighbor := by
  change neighbor ∈ [26, 27, 31, 36] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.a86c6eb98170 from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase33 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 33) :
    PartsGadgetEdgeCase 33 neighbor := by
  change neighbor ∈ [28, 29, 34] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.2673ccf9883a from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase34 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 34) :
    PartsGadgetEdgeCase 34 neighbor := by
  change neighbor ∈ [29, 30, 33, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.e8a3a6dd0caa from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase35 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 35) :
    PartsGadgetEdgeCase 35 neighbor := by
  change neighbor ∈ [30, 31, 34, 36] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.aae042a6d2ba from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase36 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 36) :
    PartsGadgetEdgeCase 36 neighbor := by
  change neighbor ∈ [31, 32, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=partsgad.1h1v.s6.5f9c17fc0c4e from=translated src=- shape=8d1778ec vocab=4d866cce
-/
lemma partsGadgetEdgeCase37 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 37) :
    PartsGadgetEdgeCase 37 neighbor := by
  change neighbor ∈ [38, 41, 42] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

end HadwigerNelsonBounds
