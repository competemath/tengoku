/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.AtomClause
import Tengoku.AclGeom.AclGeom.Config.Semantic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The soundness witness satisfies Ψ

The assembly of blueprint Theorem q-correct, soundness direction, at the
witness level: for any five algebraically independent elements
`a, b, c, d, x` of `K` over `k` (of any size), the table-7.1 witness
`qWitness` satisfies all seven clauses of `Ψ`. Consequently the semantic
quadruple `([b], [ax], [ax+b], [ax/b])` — that is,
`([u], [v], [u+v], [u/v])` for `u = b`, `v = ax` — is in the geometric
relation `QGeom`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** soundness proved over any base field, assuming the stated
supply of fresh elements. Unguarded completeness is refuted; guarded ACF completeness
is proved by `guardedQCompletenessACF` with both guards explicit (#27).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

include hind

/-- **The witness satisfies Ψ** (blueprint Thm q-correct, soundness
direction, witness verification): all seven clauses hold at the
table-7.1 points.-/
theorem qWitness_psi : (qWitness hind).Psi where
  rank_ABC := qWitness_rank_ABC hind
  rank_AB := qWitness_rank_AB hind
  rank_BC := qWitness_rank_BC hind
  rank_AC := qWitness_rank_AC hind
  X_le := qWitness_X_le hind
  Z_le := qWitness_Z_le hind
  X_notLe := qWitness_X_notLe hind
  Y_notLe := qWitness_Y_notLe hind
  Z_notLe := qWitness_Z_notLe hind
  X_free := qWitness_X_free hind
  Z_freeB := qWitness_Z_freeB hind
  Z_freeC := qWitness_Z_freeC hind
  S_le := qWitness_S_le hind
  T_le := qWitness_T_le hind
  U_le := qWitness_U_le hind
  rank_STU := qWitness_rank_STU hind
  quad := qWitness_quad hind
  meet_D := qWitness_meet_D hind
  meet_E := qWitness_meet_E hind
  meet_F := qWitness_meet_F hind
  meet_G := qWitness_meet_G hind
  meet_I := qWitness_meet_I hind
  meet_H := qWitness_meet_H hind
  meet_R := qWitness_meet_R hind

/-- The geometric `Q` holds at the four free outputs of the witness:
`([b], [ax], [ax+b], [ax/b])`.-/
theorem qGeom_of_table :
    QGeom (Point.mk' k b (qtable_b_notMem_bot hind))
      (Point.mk' k (a * x) (qtable_mul_ax_notMem_bot hind))
      (Point.mk' k (a * x + b) (qtable_Y_notMem_bot hind))
      (Point.mk' k (a * x / b) (qtable_axb_notMem_bot hind)) :=
  ⟨qWitness hind, qWitness_psi hind, rfl, rfl, rfl, rfl⟩

end

section Packaging

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- The witness generators from a semantic pair and a fresh chain: with
`u, v` independent, `a` fresh over them, and `c, d` fresh successively,
the five table generators `(a, u, c, d, v/a)` are algebraically
independent (blueprint Thm q-correct, soundness, generator step).-/
theorem qtable_indep_of_fresh {u v a c d : K}
    (hpair : AlgebraicIndependent k ![u, v])
    (ha : a ∉ racl k ({u, v} : Set K))
    (hc : c ∉ racl k ({u, v, a} : Set K))
    (hd : d ∉ racl k ({u, v, a, c} : Set K)) :
    AlgebraicIndependent k ![a, u, c, d, v / a] := by
  classical
  have huv : u ∈ racl k ({u, v} : Set K) := subset_racl k _ (by simp)
  have hvv : v ∈ racl k ({u, v} : Set K) := subset_racl k _ (by simp)
  have ha_empty : a ∉ racl k (∅ : Set K) := fun h ↦
    ha (racl_mono (Set.empty_subset _) h)
  have hu_empty : u ∉ racl k (∅ : Set K) := fun h ↦
    AlgebraicIndependent.notMem_racl_pair' hpair
      (racl_mono (Set.empty_subset _) h)
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at ha_empty
    exact ha_empty (zero_mem _)
  -- The chain facts, in build order `(a, u, v/a, c, d)`.
  have f2 : u ∉ racl k ({a} : Set K) := by
    intro h
    have h' : u ∈ racl k (insert a (∅ : Set K)) := by simpa using h
    have h2 := racl_exchange h' hu_empty
    have h3 : a ∈ racl k ({u} : Set K) := by simpa using h2
    refine ha (racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_) h3)
    exact subset_racl k _ (by simp)
  have f3 : v / a ∉ racl k ({u, a} : Set K) := by
    intro h
    have haa : a ∈ racl k ({u, a} : Set K) := subset_racl k _ (by simp)
    have hva : v ∈ racl k ({u, a} : Set K) := by
      have h2 := MulMemClass.mul_mem haa h
      rwa [mul_div_cancel₀ v ha0] at h2
    have hva' : v ∈ racl k (insert a ({u} : Set K)) := by
      rwa [Set.pair_comm u a] at hva
    have hvu : v ∉ racl k ({u} : Set K) :=
      AlgebraicIndependent.notMem_racl_pair hpair
    have h4 := racl_exchange hva' hvu
    have h5 : a ∈ racl k ({u, v} : Set K) := by
      rwa [Set.pair_comm v u] at h4
    exact ha h5
  have f4 : c ∉ racl k ({v / a, u, a} : Set K) := by
    intro h
    have hsub : racl k ({v / a, u, a} : Set K) ≤
        racl k ({u, v, a} : Set K) := by
      refine racl_le_of_subset_racl ?_
      rw [Set.insert_subset_iff, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      have hv3 : v ∈ racl k ({u, v, a} : Set K) := subset_racl k _ (by simp)
      have ha3 : a ∈ racl k ({u, v, a} : Set K) := subset_racl k _ (by simp)
      have hu3 : u ∈ racl k ({u, v, a} : Set K) := subset_racl k _ (by simp)
      have hdiv : v / a ∈ racl k ({u, v, a} : Set K) := by
        rw [div_eq_mul_inv]
        exact MulMemClass.mul_mem hv3 (inv_mem ha3)
      exact ⟨hdiv, hu3, ha3⟩
    exact hc (hsub h)
  have f5 : d ∉ racl k ({c, v / a, u, a} : Set K) := by
    intro h
    have hsub : racl k ({c, v / a, u, a} : Set K) ≤
        racl k ({u, v, a, c} : Set K) := by
      refine racl_le_of_subset_racl ?_
      rw [Set.insert_subset_iff, Set.insert_subset_iff,
        Set.insert_subset_iff, Set.singleton_subset_iff]
      have hv4 : v ∈ racl k ({u, v, a, c} : Set K) :=
        subset_racl k _ (by simp)
      have ha4 : a ∈ racl k ({u, v, a, c} : Set K) :=
        subset_racl k _ (by simp)
      have hu4 : u ∈ racl k ({u, v, a, c} : Set K) :=
        subset_racl k _ (by simp)
      have hc4 : c ∈ racl k ({u, v, a, c} : Set K) :=
        subset_racl k _ (by simp)
      refine ⟨hc4, ?_, hu4, ha4⟩
      have h2 := MulMemClass.mul_mem hv4 (inv_mem ha4)
      rwa [div_eq_mul_inv]
    exact hd (hsub h)
  -- Build the chain `(a, u, v/a, c, d)` by repeated extension.
  have t1 : AlgebraicIndependent k ![a] := by
    rw [algebraicIndependent_unique_type_iff]
    intro halg
    exact ha_empty (mem_racl_empty_of_isAlgebraic halg)
  have t2 : AlgebraicIndependent k (Fin.snoc ![a] u) := by
    refine algebraicIndependent_snoc t1 ?_
    intro h
    refine f2 ?_
    have hr : Set.range (![a] : Fin 1 → K) = {a} := by
      ext z
      simp [Matrix.range_cons, Matrix.range_empty]
    rwa [hr] at h
  have t3 : AlgebraicIndependent k (Fin.snoc (Fin.snoc ![a] u) (v / a)) := by
    refine algebraicIndependent_snoc t2 ?_
    intro h
    refine f3 ?_
    have hr : Set.range (Fin.snoc ![a] u) = {u, a} := by
      rw [Fin.range_snoc]
      have hr1 : Set.range (![a] : Fin 1 → K) = {a} := by
        ext z
        simp [Matrix.range_cons, Matrix.range_empty]
      rw [hr1]
    rwa [hr] at h
  have t4 : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc (Fin.snoc ![a] u) (v / a)) c) := by
    refine algebraicIndependent_snoc t3 ?_
    intro h
    refine f4 ?_
    have hr : Set.range (Fin.snoc (Fin.snoc ![a] u) (v / a)) =
        {v / a, u, a} := by
      rw [Fin.range_snoc, Fin.range_snoc]
      have hr1 : Set.range (![a] : Fin 1 → K) = {a} := by
        ext z
        simp [Matrix.range_cons, Matrix.range_empty]
      rw [hr1]
    rwa [hr] at h
  have t5 : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ![a] u) (v / a)) c) d) := by
    refine algebraicIndependent_snoc t4 ?_
    intro h
    refine f5 ?_
    have hr : Set.range (Fin.snoc (Fin.snoc (Fin.snoc ![a] u) (v / a)) c) =
        {c, v / a, u, a} := by
      rw [Fin.range_snoc, Fin.range_snoc, Fin.range_snoc]
      have hr1 : Set.range (![a] : Fin 1 → K) = {a} := by
        ext z
        simp [Matrix.range_cons, Matrix.range_empty]
      rw [hr1]
    rwa [hr] at h
  -- Reorder `(a, u, v/a, c, d)` to `(a, u, c, d, v/a)`.
  have h6 := AlgebraicIndependent.comp t5
    (![0, 1, 3, 4, 2] : Fin 5 → Fin 5) (by decide)
  have heq : ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ![a] u) (v / a)) c) d)
      ∘ (![0, 1, 3, 4, 2] : Fin 5 → Fin 5)) = ![a, u, c, d, v / a] := by
    funext i
    fin_cases i <;> simp
  rwa [heq] at h6

/-- **Soundness of the geometric `Q`** (blueprint Thm q-correct, one
direction): every semantic quadruple is geometric, given a supply of
fresh elements over small sets — available whenever the extension has
relative transcendence degree at least five.-/
theorem qGeom_of_qSem {X Y Z W : Point k K}
    (hfresh : ∀ S : Finset K, S.card ≤ 4 → ∃ z, z ∉ racl k (S : Set K))
    (h : QSem X Y Z W) : QGeom X Y Z W := by
  classical
  obtain ⟨u, v, hpair, hX, hY, hZ, hW⟩ := h
  obtain ⟨a, ha⟩ := hfresh {u, v} (by
    have h1 := Finset.card_insert_le u ({v} : Finset K)
    have h2 : ({v} : Finset K).card = 1 := Finset.card_singleton v
    omega)
  obtain ⟨c, hc⟩ := hfresh {u, v, a} (by
    have h1 := Finset.card_insert_le u ({v, a} : Finset K)
    have h2 := Finset.card_insert_le v ({a} : Finset K)
    have h3 : ({a} : Finset K).card = 1 := Finset.card_singleton a
    omega)
  obtain ⟨d, hd⟩ := hfresh {u, v, a, c} (by
    have h1 := Finset.card_insert_le u ({v, a, c} : Finset K)
    have h2 := Finset.card_insert_le v ({a, c} : Finset K)
    have h3 := Finset.card_insert_le a ({c} : Finset K)
    have h4 : ({c} : Finset K).card = 1 := Finset.card_singleton c
    omega)
  have ha' : a ∉ racl k ({u, v} : Set K) := by simpa using ha
  have hc' : c ∉ racl k ({u, v, a} : Set K) := by simpa using hc
  have hd' : d ∉ racl k ({u, v, a, c} : Set K) := by simpa using hd
  have hind := qtable_indep_of_fresh hpair ha' hc' hd'
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at ha'
    exact ha' (zero_mem _)
  have harith : a * (v / a) = v := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc,
      div_self ha0, mul_one]
  have hq := qGeom_of_table hind
  have e1 : Point.mk' k u (qtable_b_notMem_bot hind) = X := by
    refine Subtype.ext ?_
    rw [hX]
    rfl
  have e2 : Point.mk' k (a * (v / a)) (qtable_mul_ax_notMem_bot hind) =
      Y := by
    refine Subtype.ext ?_
    rw [hY]
    change ClosedIF.point k (a * (v / a)) = ClosedIF.point k v
    rw [harith]
  have e3 : Point.mk' k (a * (v / a) + u) (qtable_Y_notMem_bot hind) =
      Z := by
    refine Subtype.ext ?_
    rw [hZ]
    change ClosedIF.point k (a * (v / a) + u) = ClosedIF.point k (u + v)
    rw [harith, add_comm]
  have e4 : Point.mk' k (a * (v / a) / u) (qtable_axb_notMem_bot hind) =
      W := by
    refine Subtype.ext ?_
    rw [hW]
    change ClosedIF.point k (a * (v / a) / u) = ClosedIF.point k (u / v)
    rw [harith, ClosedIF.point_div_symm]
  rw [e1, e2, e3, e4] at hq
  exact hq

end Packaging

end AclGeom
