/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetData
public import Tengoku

/-! Generated central-inversion checks, group 3. -/

@[expose] public section

namespace HadwigerNelsonBounds

/--
@isnad1 id=mem.1h1v.s6.9d45efd4c889 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor57 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 57) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 57) := by
  change neighbor ∈ [51, 56, 63] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.16e5670a016d from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple57 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 57) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 57) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 57) := by
  change pair ∈ [(50, 62)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.4871987b2d49 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid57
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 57) : witness.Valid 57 := by
  change witness ∈ [
    ⟨50, 62, 50, 57, 62, true, 0, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.58a4f709c755 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor58 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 58) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 58) := by
  change neighbor ∈ [52, 53, 59, 64] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.9b58743861b3 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple58 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 58) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 58) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 58) := by
  change pair ∈ [(46, 54), (54, 65)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.6c4e30bf2240 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid58
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 58) : witness.Valid 58 := by
  change witness ∈ [
    ⟨46, 54, 46, 54, 58, true, 0, -2, true⟩,
    ⟨54, 65, 65, 58, 54, true, 1, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.152c804a4380 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor59 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 59) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 59) := by
  change neighbor ∈ [53, 54, 58, 60, 64, 65] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.3ef6b181bdee from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple59 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 59) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 59) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 59) := by
  change pair ∈ [(18, 47), (18, 66), (47, 52), (66, 69)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.d9ffc37df86e from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid59
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 59) : witness.Valid 59 := by
  change witness ∈ [
    ⟨18, 47, 47, 18, 59, true, 0, -1, true⟩,
    ⟨18, 66, 66, 59, 18, true, 1, -1, false⟩,
    ⟨47, 52, 59, 52, 47, true, 0, -2, false⟩,
    ⟨66, 69, 59, 66, 69, true, 2, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.3548b635b4be from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor60 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 60) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 60) := by
  change neighbor ∈ [18, 54, 59, 61, 65, 66] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.e5927e0211fd from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple60 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 60) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 60) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 60) := by
  change pair ∈ [(48, 53), (48, 55), (53, 64), (55, 67), (64, 70), (67, 70)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.e0c9f49af504 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid60
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 60) : witness.Valid 60 := by
  change witness ∈ [
    ⟨48, 53, 60, 53, 48, true, 0, -1, false⟩,
    ⟨48, 55, 48, 55, 60, true, 0, 0, true⟩,
    ⟨53, 64, 53, 60, 64, true, 1, -2, true⟩,
    ⟨55, 67, 67, 60, 55, true, 1, 0, false⟩,
    ⟨64, 70, 70, 64, 60, true, 2, -2, false⟩,
    ⟨67, 70, 60, 67, 70, true, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.327fff2d291b from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor61 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 61) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 61) := by
  change neighbor ∈ [18, 55, 60, 62, 66, 67] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.4c714bd222ef from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple61 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 61) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 61) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 61) := by
  change pair ∈ [(49, 54), (49, 56), (54, 65), (56, 68), (65, 71), (68, 71)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.cafa57c5292a from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid61
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 61) : witness.Valid 61 := by
  change witness ∈ [
    ⟨49, 54, 61, 54, 49, true, 0, 0, false⟩,
    ⟨49, 56, 49, 56, 61, true, 0, 1, true⟩,
    ⟨54, 65, 54, 61, 65, true, 1, -1, true⟩,
    ⟨56, 68, 68, 61, 56, true, 1, 1, false⟩,
    ⟨65, 71, 71, 65, 61, true, 2, -1, false⟩,
    ⟨68, 71, 61, 68, 71, true, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.3b14424af9f4 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor62 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 62) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 62) := by
  change neighbor ∈ [55, 56, 61, 63, 67, 68] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.de6600152f5a from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple62 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 62) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 62) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 62) := by
  change pair ∈ [(18, 50), (18, 66), (50, 57), (66, 72)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.14b37f1478fc from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid62
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 62) : witness.Valid 62 := by
  change witness ∈ [
    ⟨18, 50, 62, 18, 50, true, 0, 1, false⟩,
    ⟨18, 66, 18, 62, 66, true, 1, 0, true⟩,
    ⟨50, 57, 50, 57, 62, true, 0, 2, true⟩,
    ⟨66, 72, 72, 66, 62, true, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.cd3f78262482 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor63 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 63) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 63) := by
  change neighbor ∈ [56, 57, 62, 68] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.44a467858b82 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple63 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 63) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 63) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 63) := by
  change pair ∈ [(51, 55), (55, 67)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.d2a0b5e6a7c2 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid63
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 63) : witness.Valid 63 := by
  change witness ∈ [
    ⟨51, 55, 63, 55, 51, true, 0, 2, false⟩,
    ⟨55, 67, 55, 63, 67, true, 1, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.6f59a7294491 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor64 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 64) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 64) := by
  change neighbor ∈ [58, 59, 65, 69] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.8cab1582d60e from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple64 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 64) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 64) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 64) := by
  change pair ∈ [(53, 60), (60, 70)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.dc1504de6d01 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid64
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 64) : witness.Valid 64 := by
  change witness ∈ [
    ⟨53, 60, 53, 60, 64, true, 1, -2, true⟩,
    ⟨60, 70, 70, 64, 60, true, 2, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.b3d6000610cb from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor65 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 65) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 65) := by
  change neighbor ∈ [29, 59, 60, 64, 66, 69, 70] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.1ebe273c5cab from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple65 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 65) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 65) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 65) := by
  change pair ∈ [(54, 58), (54, 61), (61, 71)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.e069773ab9b5 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid65
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 65) : witness.Valid 65 := by
  change witness ∈ [
    ⟨54, 58, 65, 58, 54, true, 1, -2, false⟩,
    ⟨54, 61, 54, 61, 65, true, 1, -1, true⟩,
    ⟨61, 71, 71, 65, 61, true, 2, -1, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.2ebb0c63cb7e from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor66 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 66) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 66) := by
  change neighbor ∈ [60, 61, 65, 67, 70, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.612c7705c2d0 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple66 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 66) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 66) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 66) := by
  change pair ∈ [(18, 59), (18, 62), (59, 69), (62, 72)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.abf433d66bbe from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid66
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 66) : witness.Valid 66 := by
  change witness ∈ [
    ⟨18, 59, 66, 59, 18, true, 1, -1, false⟩,
    ⟨18, 62, 18, 62, 66, true, 1, 0, true⟩,
    ⟨59, 69, 59, 66, 69, true, 2, -2, true⟩,
    ⟨62, 72, 72, 66, 62, true, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.d1eeb860422f from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor67 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 67) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 67) := by
  change neighbor ∈ [31, 61, 62, 66, 68, 71, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.934c2117dbcc from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple67 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 67) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 67) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 67) := by
  change pair ∈ [(55, 60), (55, 63), (60, 70)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.0c176b96e9f4 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid67
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 67) : witness.Valid 67 := by
  change witness ∈ [
    ⟨55, 60, 67, 60, 55, true, 1, 0, false⟩,
    ⟨55, 63, 55, 63, 67, true, 1, 1, true⟩,
    ⟨60, 70, 60, 67, 70, true, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.f6adcf51af7f from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor68 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 68) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 68) := by
  change neighbor ∈ [62, 63, 67, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.72aec027db34 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple68 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 68) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 68) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 68) := by
  change pair ∈ [(56, 61), (61, 71)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.683b1274165c from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid68
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 68) : witness.Valid 68 := by
  change witness ∈ [
    ⟨56, 61, 68, 61, 56, true, 1, 1, false⟩,
    ⟨61, 71, 61, 68, 71, true, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.956370d07c84 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor69 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 69) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 69) := by
  change neighbor ∈ [64, 65, 70] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.18d37bea6de3 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple69 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 69) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 69) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 69) := by
  change pair ∈ [(59, 66)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.2c9218969aee from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid69
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 69) : witness.Valid 69 := by
  change witness ∈ [
    ⟨59, 66, 59, 66, 69, true, 2, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.9d71e4807d93 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor70 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 70) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 70) := by
  change neighbor ∈ [65, 66, 69, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.2e64dad0468c from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple70 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 70) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 70) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 70) := by
  change pair ∈ [(60, 64), (60, 67)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.6858d7e8c2f2 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid70
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 70) : witness.Valid 70 := by
  change witness ∈ [
    ⟨60, 64, 70, 64, 60, true, 2, -2, false⟩,
    ⟨60, 67, 60, 67, 70, true, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.d8c84c5df20e from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor71 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 71) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 71) := by
  change neighbor ∈ [66, 67, 70, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.ab69e329dd05 from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple71 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 71) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 71) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 71) := by
  change pair ∈ [(61, 65), (61, 68)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.78dd1ca88a40 from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid71
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 71) : witness.Valid 71 := by
  change witness ∈ [
    ⟨61, 65, 71, 65, 61, true, 2, -1, false⟩,
    ⟨61, 68, 61, 68, 71, true, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

/--
@isnad1 id=mem.1h1v.s6.e4f6dc338a47 from=translated src=- shape=0a9de518 vocab=60785ee8
-/
lemma partsGadgetNegationNeighbor72 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 72) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 72) := by
  change neighbor ∈ [67, 68, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

/--
@isnad1 id=or.1h1v.s8.b5d95e31c08b from=translated src=- shape=010a2727 vocab=ca59a351
-/
lemma partsGadgetNegationTriple72 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 72) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 72) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 72) := by
  change pair ∈ [(62, 66)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

/--
@isnad1 id=valid.1h1v.s5.68ddecc08edf from=translated src=- shape=4d44e7ff vocab=6466247a
-/
lemma partsGadgetTriangleWitnessValid72
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 72) : witness.Valid 72 := by
  change witness ∈ [
    ⟨62, 66, 72, 66, 62, true, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

end HadwigerNelsonBounds
