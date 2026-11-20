/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.Construction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

theorem incidence_triple_sum (p q r : P) :
    (∑ e, D.incidence p e * D.incidence q e * D.incidence r e) =
      2 + 9 * (if p = q then 1 else 0) + 9 * (if p = r then 1 else 0) +
        9 * (if q = r then 1 else 0) + 27 * (if p = q ∧ p = r then 1 else 0) := by
  have hsum : (∑ e, D.incidence p e * D.incidence q e * D.incidence r e) =
      ((Finset.univ.filter fun e => p ∈ D.block e ∧ q ∈ D.block e ∧ r ∈ D.block e).card : ℤ) := by
    simp only [incidence, ite_zero_mul_ite_zero, one_mul, Finset.sum_boole, and_assoc]
  rw [hsum]
  by_cases hpq : p = q
  · subst q
    by_cases hpr : p = r
    · subst r
      simp [D.replication]
    · simp [hpr, D.point_pair p r hpr]
  · by_cases hpr : p = r
    · subst r
      have heq : (Finset.univ.filter fun e => p ∈ D.block e ∧ q ∈ D.block e ∧ p ∈ D.block e) =
          Finset.univ.filter fun e => p ∈ D.block e ∧ q ∈ D.block e := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,h.1⟩⟩
      rw [heq, D.point_pair p q hpq]
      simp [hpq, Ne.symm hpq]
    · by_cases hqr : q = r
      · subst r
        simp [hpq, D.point_pair p q hpq]
      · rw [D.point_triple p q r hpq hpr hqr]
        simp [hpq, hpr, hqr]

def subsetTrace (S : Finset P) (e : B) : ℤ := ∑ p ∈ S, D.incidence p e

@[simp] theorem subsetTrace_singleton (p : P) (e : B) :
    D.subsetTrace {p} e = D.incidence p e := by simp [subsetTrace]

theorem subsetTrace_block (b e : B) :
    D.subsetTrace (D.block b) e = ((D.block b ∩ D.block e).card : ℤ) := by
  simp [subsetTrace, incidence]

theorem triple_subsetTrace_expand (S T U : Finset P) :
    (∑ e, D.subsetTrace S e * D.subsetTrace T e * D.subsetTrace U e) =
      ∑ p ∈ S, ∑ q ∈ T, ∑ r ∈ U,
        (2 + 9 * (if p = q then 1 else 0) + 9 * (if p = r then 1 else 0) +
          9 * (if q = r then 1 else 0) + 27 * (if p = q ∧ p = r then 1 else 0)) := by
  have hprod (e : B) : D.subsetTrace S e * D.subsetTrace T e * D.subsetTrace U e =
      ∑ p ∈ S, ∑ q ∈ T, ∑ r ∈ U, D.incidence p e * D.incidence q e * D.incidence r e := by
    simp only [subsetTrace, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := U) (t := T)]
    simp_rw [Finset.sum_comm (s := U) (t := S)]
    rw [Finset.sum_comm (s := T) (t := S)]
  simp_rw [hprod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r hr => D.incidence_triple_sum p q r

theorem triple_subsetTrace_sum (S T U : Finset P) :
    (∑ e, D.subsetTrace S e * D.subsetTrace T e * D.subsetTrace U e) =
      2 * (S.card : ℤ) * T.card * U.card +
        9 * ((S ∩ T).card * (U.card : ℤ) + (S ∩ U).card * (T.card : ℤ) +
          (T ∩ U).card * (S.card : ℤ)) + 27 * (S ∩ T ∩ U).card := by
  have hdiag : (∑ p ∈ S, ∑ q ∈ T, ∑ r ∈ U,
      (if p = q ∧ p = r then (1 : ℤ) else 0)) = (S ∩ T ∩ U).card := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq]
    simp only [← ite_and, Finset.sum_boole]
    congr 2
    ext p
    simp
  rw [D.triple_subsetTrace_expand]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hdiag]
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.sum_boole, Finset.filter_mem_eq_inter]
  ring

theorem block_intersection_three {b c : B} (hbc : b ≠ c)
    (hnot : (D.block b ∩ D.block c).card ≠ 0) : (D.block b ∩ D.block c).card = 3 :=
  (D.block_intersections b c hbc).resolve_left hnot

theorem point_point_block_moment {p q : P} {b : B} (hpq : p ≠ q)
    (hp : p ∉ D.block b) (hq : q ∉ D.block b) :
    (∑ e, D.incidence p e * D.incidence q e * D.subsetTrace (D.block b) e) = 24 := by
  have h := D.triple_subsetTrace_sum {p} {q} (D.block b)
  simpa [hpq, hp, hq, D.block_size] using h

theorem point_block_block_moment {p : P} {b c : B}
    (hp : p ∉ D.block b) (hq : p ∉ D.block c)
    (hbc : (D.block b ∩ D.block c).card = 3) :
    (∑ e, D.incidence p e * D.subsetTrace (D.block b) e * D.subsetTrace (D.block c) e) = 315 := by
  have h := D.triple_subsetTrace_sum {p} (D.block b) (D.block c)
  simpa [hp, hq, hbc, D.block_size] using h

theorem block_block_block_moment {b c d : B}
    (hbc : (D.block b ∩ D.block c).card = 3)
    (hbd : (D.block b ∩ D.block d).card = 3)
    (hcd : (D.block c ∩ D.block d).card = 3) :
    (∑ e, D.subsetTrace (D.block b) e * D.subsetTrace (D.block c) e *
      D.subsetTrace (D.block d) e) = 4428 + 27 * (D.block b ∩ D.block c ∩ D.block d).card := by
  have h := D.triple_subsetTrace_sum (D.block b) (D.block c) (D.block d)
  simpa [hbc, hbd, hcd, D.block_size] using h

theorem subsetTrace_block_affine (b e : B) :
    D.subsetTrace (D.block b) e = 3 - 3 * D.disjointness b e + 9 * (if e = b then 1 else 0) := by
  rw [D.subsetTrace_block]
  have h := congrFun (congrFun D.incidence_block_gram b) e
  rw [D.incidence_block_gram_apply] at h
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    allOnesMatrix_apply, Matrix.one_apply] at h
  by_cases heb : e = b
  · subst e
    simp only [ite_true] at h ⊢
    omega
  · simp only [ite_eq_right heb, ite_eq_right (Ne.symm heb), mul_zero, add_zero] at h ⊢
    omega

theorem incidence_mul_disjointness_sum (p : P) (b : B) :
    (∑ e, D.incidence p e * D.disjointness b e) = 12 - 12 * D.incidence p b := by
  have h := congrFun (congrFun D.incidence_mul_disjointness p) b
  simpa [Matrix.mul_apply, D.disjointness_comm b, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, allOnesMatrix, mul_sub] using h

theorem disjointness_pair_sum {b c : B} (hbc : b ≠ c)
    (hnot : (D.block b ∩ D.block c).card ≠ 0) :
    (∑ e, D.disjointness b e * D.disjointness c e) = 9 := by
  have h := congrFun (congrFun D.disjointness_square b) c
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, ite_eq_right hbc,
    allOnesMatrix_apply] at h
  have hA : D.disjointness b c = 0 := by simp [disjointness, hnot]
  rw [hA] at h
  simpa only [← D.disjointness_comm c, mul_zero, mul_one, sub_zero, zero_add] using h

theorem point_point_disjoint_triple {p q : P} {b : B} (hpq : p ≠ q)
    (hp : p ∉ D.block b) (hq : q ∉ D.block b) :
    (∑ e, D.incidence p e * D.incidence q e * D.disjointness b e) = 3 := by
  have h := D.point_point_block_moment hpq hp hq
  have hG := D.incidence_point_gram_apply p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ite_eq_right hpq] at hG
  have hentry (e : B) : D.incidence p e * D.incidence q e * D.subsetTrace (D.block b) e =
      3 * (D.incidence p e * D.incidence q e) -
        3 * (D.incidence p e * D.incidence q e * D.disjointness b e) := by
    rw [D.subsetTrace_block_affine]
    by_cases heb : e = b
    · subst e
      simp [incidence, hp]
    · simp only [ite_eq_right heb, mul_zero, add_zero]
      ring
  simp_rw [hentry] at h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hG] at h
  omega

theorem point_disjoint_disjoint_triple {p : P} {b c : B}
    (hp : p ∉ D.block b) (hq : p ∉ D.block c)
    (hbc : (D.block b ∩ D.block c).card = 3) :
    (∑ e, D.incidence p e * D.disjointness b e * D.disjointness c e) = 3 := by
  have h := D.point_block_block_moment hp hq hbc
  have hentry (e : B) : D.incidence p e * D.subsetTrace (D.block b) e *
      D.subsetTrace (D.block c) e =
      9 * D.incidence p e - 9 * (D.incidence p e * D.disjointness b e) -
        9 * (D.incidence p e * D.disjointness c e) +
          9 * (D.incidence p e * D.disjointness b e * D.disjointness c e) := by
    rw [D.subsetTrace_block_affine, D.subsetTrace_block_affine]
    by_cases heb : e = b
    · subst e
      simp [incidence, hp]
    by_cases hec : e = c
    · subst e
      simp [incidence, hq]
    simp only [ite_eq_right heb, ite_eq_right hec, mul_zero, add_zero]
    ring
  simp_rw [hentry] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [D.incidence_row_sum, D.incidence_mul_disjointness_sum,
    D.incidence_mul_disjointness_sum] at h
  have hpb : D.incidence p b = 0 := by simp [incidence, hp]
  have hpc : D.incidence p c = 0 := by simp [incidence, hq]
  rw [hpb,hpc] at h
  omega

theorem three_disjoint_triple_complement {b c d : B}
    (hbcne : b ≠ c) (hbdne : b ≠ d) (hcdne : c ≠ d)
    (hbc : (D.block b ∩ D.block c).card = 3)
    (hbd : (D.block b ∩ D.block d).card = 3)
    (hcd : (D.block c ∩ D.block d).card = 3) :
    (∑ e, D.disjointness b e * D.disjointness c e * D.disjointness d e) +
      (D.block b ∩ D.block c ∩ D.block d).card = 3 := by
  have h := D.block_block_block_moment hbc hbd hcd
  have hbc0 : D.disjointness b c = 0 := by simp [disjointness,hbc]
  have hbd0 : D.disjointness b d = 0 := by simp [disjointness,hbd]
  have hcd0 : D.disjointness c d = 0 := by simp [disjointness,hcd]
  have hcb0 : D.disjointness c b = 0 := (D.disjointness_comm c b).trans hbc0
  have hdb0 : D.disjointness d b = 0 := (D.disjointness_comm d b).trans hbd0
  have hdc0 : D.disjointness d c = 0 := (D.disjointness_comm d c).trans hcd0
  have hentry (e : B) : D.subsetTrace (D.block b) e * D.subsetTrace (D.block c) e *
      D.subsetTrace (D.block d) e =
      27 * (1 - D.disjointness b e - D.disjointness c e - D.disjointness d e +
        D.disjointness b e * D.disjointness c e + D.disjointness b e * D.disjointness d e +
        D.disjointness c e * D.disjointness d e -
          D.disjointness b e * D.disjointness c e * D.disjointness d e) +
      81 * ((if e = b then 1 else 0) + (if e = c then 1 else 0) +
        (if e = d then 1 else 0)) := by
    simp only [D.subsetTrace_block_affine]
    by_cases heb : e = b
    · subst e
      simp [D.disjointness_diag,hcb0,hdb0,hbcne,hbdne]
    by_cases hec : e = c
    · subst e
      simp [D.disjointness_diag,hbc0,hdc0,Ne.symm hbcne,hcdne]
    by_cases hed : e = d
    · subst e
      simp [D.disjointness_diag,hbd0,hcd0,Ne.symm hbdne,Ne.symm hcdne]
    simp only [ite_eq_right heb, ite_eq_right hec, ite_eq_right hed, mul_zero, add_zero]
    ring
  simp_rw [hentry] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, D.index_card,
    D.disjointness_row_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [D.disjointness_pair_sum hbcne (by omega),
    D.disjointness_pair_sum hbdne (by omega),
    D.disjointness_pair_sum hcdne (by omega)] at h
  omega

theorem independent_triple_neighbor_moment (x y z : KreinVertex (P := P) (B := B))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (nxy : ¬ D.kreinGraph.Adj x y) (nxz : ¬ D.kreinGraph.Adj x z)
    (nyz : ¬ D.kreinGraph.Adj y z) :
    (∑ w, D.kreinMatrix x w * D.kreinMatrix y w * D.kreinMatrix z w) = 3 := by
  rcases x with _ | (p | b) <;> rcases y with _ | (q | c) <;> rcases z with _ | (r | d)
  all_goals try exact (hxy rfl).elim
  all_goals try exact (hxz rfl).elim
  all_goals try exact (hyz rfl).elim
  all_goals simp only [kreinGraph, kreinAdj, not_true_eq_false] at nxy nxz nyz
  all_goals simp only [ne_eq, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq] at hxy hxz hyz
  all_goals rw [Fintype.sum_option, Fintype.sum_sum_type]
  all_goals simp only [kreinMatrix, mul_zero, zero_mul, mul_one, one_mul,
    zero_add, add_zero, Finset.sum_const_zero]
  · change (D.incidence.transpose * D.incidence) c d = 3
    rw [D.incidence_block_gram_apply, D.block_intersection_three hyz nyz]
    norm_num
  · rw [D.incidence_triple_sum]
    simp [hxy,hxz,hyz]
  · exact D.point_point_disjoint_triple hxy nxz nyz
  · simpa only [mul_right_comm] using D.point_point_disjoint_triple hxz nxy nyz
  · exact D.point_disjoint_disjoint_triple nxy nxz (D.block_intersection_three hyz nyz)
  · change (D.incidence.transpose * D.incidence) b d = 3
    rw [D.incidence_block_gram_apply, D.block_intersection_three hxz nxz]
    norm_num
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using D.point_point_disjoint_triple hyz nxy nxz
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      D.point_disjoint_disjoint_triple nxy nyz (D.block_intersection_three hxz nxz)
  · change (D.incidence.transpose * D.incidence) b c = 3
    rw [D.incidence_block_gram_apply, D.block_intersection_three hxy nxy]
    norm_num
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      D.point_disjoint_disjoint_triple nxz nyz (D.block_intersection_three hxy nxy)
  · have hinc : (∑ p, D.incidence p b * D.incidence p c * D.incidence p d) =
        ((D.block b ∩ D.block c ∩ D.block d).card : ℤ) := by
      simp [incidence, Finset.inter_comm, Finset.inter_assoc]
    rw [hinc,add_comm]
    exact D.three_disjoint_triple_complement hxy hxz hyz
      (D.block_intersection_three hxy nxy) (D.block_intersection_three hxz nxz)
      (D.block_intersection_three hyz nyz)

end SRG266.QuasiSymmetric.TripleDesign57
