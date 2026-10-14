/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetData
public import Tengoku

/-! Generated central-inversion checks, group 1. -/

@[expose] public section

namespace HadwigerNelsonBounds

/--
@isnad1 id=mem.1h1v.s6.83c2c872aa1d from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor19 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 19) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 19) := by
  change neighbor ∈ [12, 13, 18, 20, 25, 26] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.58ade0a9e9ea from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple19 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 19) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 19) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 19) := by
  change pair ∈ [(7, 11), (7, 14), (11, 24), (14, 27), (24, 31), (27, 31)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.442d9e484410 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid19
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 19) : witness.Valid 19 := by
  change witness ∈ [
    ⟨7, 11, 19, 11, 7, false, -1, 1, false⟩,
    ⟨7, 14, 7, 14, 19, false, -1, 2, true⟩,
    ⟨11, 24, 11, 19, 24, false, 0, 0, true⟩,
    ⟨14, 27, 27, 19, 14, false, 0, 2, false⟩,
    ⟨24, 31, 31, 24, 19, false, 1, 0, false⟩,
    ⟨27, 31, 19, 27, 31, false, 1, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.4add3e9eba05 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor20 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 20) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 20) := by
  change neighbor ∈ [13, 14, 19, 21, 26, 27, 56] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.d09384facbe7 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple20 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 20) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 20) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 20) := by
  change pair ∈ [(8, 12), (12, 25), (25, 32)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.22078bb8d5f1 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid20
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 20) : witness.Valid 20 := by
  change witness ∈ [
    ⟨8, 12, 20, 12, 8, false, -1, 2, false⟩,
    ⟨12, 25, 12, 20, 25, false, 0, 1, true⟩,
    ⟨25, 32, 32, 25, 20, false, 1, 1, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.4fd3b32c1cd0 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor21 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 21) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 21) := by
  change neighbor ∈ [14, 20, 27] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.a4bce2c7458e from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple21 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 21) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 21) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 21) := by
  change pair ∈ [(13, 26)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.4a0271914d2a from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid21
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 21) : witness.Valid 21 := by
  change witness ∈ [
    ⟨13, 26, 13, 21, 26, false, 0, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.47173f3654f8 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor22 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 22) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 22) := by
  change neighbor ∈ [15, 16, 23, 28] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.c71dce04d2fa from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple22 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 22) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 22) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 22) := by
  change pair ∈ [(9, 17), (17, 29)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.ad28c61de965 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid22
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 22) : witness.Valid 22 := by
  change witness ∈ [
    ⟨9, 17, 9, 17, 22, false, 0, -2, true⟩,
    ⟨17, 29, 29, 22, 17, false, 1, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.24781a0b4d79 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor23 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 23) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 23) := by
  change neighbor ∈ [16, 17, 22, 24, 28, 29] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.2a509d504450 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple23 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 23) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 23) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 23) := by
  change pair ∈ [(10, 15), (10, 18), (18, 30), (30, 33)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.f03dc34a6c56 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid23
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 23) : witness.Valid 23 := by
  change witness ∈ [
    ⟨10, 15, 23, 15, 10, false, 0, -2, false⟩,
    ⟨10, 18, 10, 18, 23, false, 0, -1, true⟩,
    ⟨18, 30, 30, 23, 18, false, 1, -1, false⟩,
    ⟨30, 33, 23, 30, 33, false, 2, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.c6d0af87533b from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor24 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 24) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 24) := by
  change neighbor ∈ [17, 18, 23, 25, 29, 30] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.59840f8ad6c9 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple24 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 24) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 24) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 24) := by
  change pair ∈ [(11, 16), (11, 19), (16, 28), (19, 31), (28, 34), (31, 34)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.70e9651a1d3c from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid24
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 24) : witness.Valid 24 := by
  change witness ∈ [
    ⟨11, 16, 24, 16, 11, false, 0, -1, false⟩,
    ⟨11, 19, 11, 19, 24, false, 0, 0, true⟩,
    ⟨16, 28, 16, 24, 28, false, 1, -2, true⟩,
    ⟨19, 31, 31, 24, 19, false, 1, 0, false⟩,
    ⟨28, 34, 34, 28, 24, false, 2, -2, false⟩,
    ⟨31, 34, 24, 31, 34, false, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.f135c2d1055b from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor25 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 25) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 25) := by
  change neighbor ∈ [18, 19, 24, 26, 30, 31] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.523d3989926e from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple25 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 25) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 25) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 25) := by
  change pair ∈ [(12, 17), (12, 20), (17, 29), (20, 32), (29, 35), (32, 35)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.3a0b8b5fc8a1 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid25
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 25) : witness.Valid 25 := by
  change witness ∈ [
    ⟨12, 17, 25, 17, 12, false, 0, 0, false⟩,
    ⟨12, 20, 12, 20, 25, false, 0, 1, true⟩,
    ⟨17, 29, 17, 25, 29, false, 1, -1, true⟩,
    ⟨20, 32, 32, 25, 20, false, 1, 1, false⟩,
    ⟨29, 35, 35, 29, 25, false, 2, -1, false⟩,
    ⟨32, 35, 25, 32, 35, false, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.66279d6b51cf from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor26 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 26) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 26) := by
  change neighbor ∈ [19, 20, 25, 27, 31, 32] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.b32281019542 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple26 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 26) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 26) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 26) := by
  change pair ∈ [(13, 18), (13, 21), (18, 30), (30, 36)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.af0f8327fb23 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid26
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 26) : witness.Valid 26 := by
  change witness ∈ [
    ⟨13, 18, 26, 18, 13, false, 0, 1, false⟩,
    ⟨13, 21, 13, 21, 26, false, 0, 2, true⟩,
    ⟨18, 30, 18, 26, 30, false, 1, 0, true⟩,
    ⟨30, 36, 36, 30, 26, false, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.c02d4fa2bf74 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor27 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 27) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 27) := by
  change neighbor ∈ [20, 21, 26, 32] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.e1c8d6457302 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple27 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 27) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 27) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 27) := by
  change pair ∈ [(14, 19), (19, 31)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.e3cd1003bab7 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid27
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 27) : witness.Valid 27 := by
  change witness ∈ [
    ⟨14, 19, 27, 19, 14, false, 0, 2, false⟩,
    ⟨19, 31, 19, 27, 31, false, 1, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.6fde05fad8f3 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor28 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 28) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 28) := by
  change neighbor ∈ [22, 23, 29, 33] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.3a93dafce329 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple28 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 28) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 28) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 28) := by
  change pair ∈ [(16, 24), (24, 34)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.16742a1a5f63 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid28
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 28) : witness.Valid 28 := by
  change witness ∈ [
    ⟨16, 24, 16, 24, 28, false, 1, -2, true⟩,
    ⟨24, 34, 34, 28, 24, false, 2, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.e48326f42738 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor29 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 29) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 29) := by
  change neighbor ∈ [23, 24, 28, 30, 33, 34, 65] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.0d6b544fc0f0 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple29 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 29) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 29) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 29) := by
  change pair ∈ [(17, 22), (17, 25), (25, 35)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.5224886d3016 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid29
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 29) : witness.Valid 29 := by
  change witness ∈ [
    ⟨17, 22, 29, 22, 17, false, 1, -2, false⟩,
    ⟨17, 25, 17, 25, 29, false, 1, -1, true⟩,
    ⟨25, 35, 35, 29, 25, false, 2, -1, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.e675322774e2 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor30 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 30) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 30) := by
  change neighbor ∈ [24, 25, 29, 31, 34, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.846d3125e9d0 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple30 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 30) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 30) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 30) := by
  change pair ∈ [(18, 23), (18, 26), (23, 33), (26, 36)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.be796c21933c from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid30
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 30) : witness.Valid 30 := by
  change witness ∈ [
    ⟨18, 23, 30, 23, 18, false, 1, -1, false⟩,
    ⟨18, 26, 18, 26, 30, false, 1, 0, true⟩,
    ⟨23, 33, 23, 30, 33, false, 2, -2, true⟩,
    ⟨26, 36, 36, 30, 26, false, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.d5d862e52364 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor31 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 31) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 31) := by
  change neighbor ∈ [25, 26, 30, 32, 35, 36, 67] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.dc24af8c9733 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple31 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 31) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 31) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 31) := by
  change pair ∈ [(19, 24), (19, 27), (24, 34)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.061f1bc31e27 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid31
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 31) : witness.Valid 31 := by
  change witness ∈ [
    ⟨19, 24, 31, 24, 19, false, 1, 0, false⟩,
    ⟨19, 27, 19, 27, 31, false, 1, 1, true⟩,
    ⟨24, 34, 24, 31, 34, false, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.925412874035 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor32 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 32) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 32) := by
  change neighbor ∈ [26, 27, 31, 36] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.22340c11c621 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple32 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 32) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 32) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 32) := by
  change pair ∈ [(20, 25), (25, 35)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.e48944bed67f from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid32
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 32) : witness.Valid 32 := by
  change witness ∈ [
    ⟨20, 25, 32, 25, 20, false, 1, 1, false⟩,
    ⟨25, 35, 25, 32, 35, false, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.13c9d37fd66b from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor33 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 33) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 33) := by
  change neighbor ∈ [28, 29, 34] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.ec3d990a938c from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple33 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 33) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 33) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 33) := by
  change pair ∈ [(23, 30)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.bc05197a75b4 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid33
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 33) : witness.Valid 33 := by
  change witness ∈ [
    ⟨23, 30, 23, 30, 33, false, 2, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.cfdf7f08a22c from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor34 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 34) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 34) := by
  change neighbor ∈ [29, 30, 33, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.ea10e5c6b6c4 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple34 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 34) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 34) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 34) := by
  change pair ∈ [(24, 28), (24, 31)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.dae78793c3c0 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid34
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 34) : witness.Valid 34 := by
  change witness ∈ [
    ⟨24, 28, 34, 28, 24, false, 2, -2, false⟩,
    ⟨24, 31, 24, 31, 34, false, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.0c4fc4e472e6 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor35 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 35) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 35) := by
  change neighbor ∈ [30, 31, 34, 36] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.52424f2d92c3 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple35 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 35) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 35) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 35) := by
  change pair ∈ [(25, 29), (25, 32)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.1c1ff4326c27 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid35
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 35) : witness.Valid 35 := by
  change witness ∈ [
    ⟨25, 29, 35, 29, 25, false, 2, -1, false⟩,
    ⟨25, 32, 25, 32, 35, false, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.25edfe530a24 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor36 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 36) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 36) := by
  change neighbor ∈ [31, 32, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.8aa10be91586 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple36 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 36) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 36) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 36) := by
  change pair ∈ [(26, 30)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.514f821d4063 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid36
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 36) : witness.Valid 36 := by
  change witness ∈ [
    ⟨26, 30, 36, 30, 26, false, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.f0274bd56ef7 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor37 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 37) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 37) := by
  change neighbor ∈ [38, 41, 42] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.c96fef0611e7 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple37 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 37) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 37) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 37) := by
  change pair ∈ [(43, 47)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.a6b8d3c54781 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid37
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 37) : witness.Valid 37 := by
  change witness ∈ [
    ⟨43, 47, 37, 43, 47, true, -2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

end HadwigerNelsonBounds
