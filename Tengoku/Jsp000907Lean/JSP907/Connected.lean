/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Tengoku.Jsp000907Lean.JSP907.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The hub-free part of `G m` is connected

We phrase connectivity as a closure principle: a set of vertices which is closed under
passing from a non-hub vertex to all of its neighbours, and which contains one non-hub
vertex, contains every non-hub vertex.
-/

namespace JSP907

variable {m : ℕ}

/--
@isnad1 id=or.0h2v.s8.3fc96330f713 from=translated src=- shape=8ca0fdf7 vocab=c21ac8e2
-/
lemma pos_shift (y y' : Pos) :
    y' = y ∨ y' = y + 1 ∨ y' = y + 1 + 1 ∨ y' = y + 1 + 1 + 1 ∨ y' = y + 1 + 1 + 1 + 1 := by
  revert y y'
  decide

/-- The leaf-to-spine edge.
@isnad1 id=adj.0h2v.s7.54b36f9aa496 from=translated src=- shape=1f5d07f1 vocab=fec77942
-/
lemma adj_attach' (L : LIdx m) :
    (G m).Adj (some (Sum.inr L, L.1.2)) (some (Sum.inl ⟨L.1.1, L.2.1⟩, L.1.2)) := by
  refine Or.inr (Or.inl ?_)
  rw [ext_inr, extL, ite_eq_left rfl]

section Closure

variable (T : Set (Vtx m))
  (hT : ∀ p : Blk m × Pos, some p ∈ T → ∀ v, (G m).Adj (some p) v → v ∈ T)

include hT

/--
@isnad1 id=mem.2h4v.s7.04593f0b7528 from=translated src=- shape=e458595a vocab=144c50c7
-/
lemma closure_step (B : Blk m) (z : Pos) (h : some (B, z) ∈ T) : some (B, z + 1) ∈ T :=
  hT _ h _ (adj_block B (Or.inl rfl))

/--
@isnad1 id=mem.2h5v.s6.a98055c1054a from=translated src=- shape=e8aad566 vocab=88aa23fb
-/
lemma closure_block (B : Blk m) (y y' : Pos) (h : some (B, y) ∈ T) : some (B, y') ∈ T := by
  have h1 := closure_step T hT B y h
  have h2 := closure_step T hT B _ h1
  have h3 := closure_step T hT B _ h2
  have h4 := closure_step T hT B _ h3
  rcases pos_shift y y' with rfl | rfl | rfl | rfl | rfl
  exacts [h, h1, h2, h3, h4]

/-- From a spine block one reaches the leaf blocks hanging from it.
@isnad1 id=mem.3h5v.s8.8b270af62821 from=translated src=- shape=b47735ae vocab=2aa9e856
-/
lemma closure_spine_to_leaf (S : SIdx m) (x : Pos) (hx : LeafOK m S.1 x)
    (h : ∀ y : Pos, some (Sum.inl S, y) ∈ T) (y : Pos) :
    some (Sum.inr (⟨(S.1, x), ⟨S.2, hx⟩⟩ : LIdx m), y) ∈ T :=
  closure_block T hT _ x y (hT _ (h x) _ (adj_attach S hx))

/-- From a leaf block one reaches the spine block it hangs from.
@isnad1 id=mem.2h4v.s7.3253d3692ef3 from=translated src=- shape=4ee73c76 vocab=79fa7cc0
-/
lemma closure_leaf_to_spine (L : LIdx m) (h : some (Sum.inr L, L.1.2) ∈ T) (y : Pos) :
    some (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m), y) ∈ T :=
  closure_block T hT _ L.1.2 y (hT _ h _ (adj_attach' L))

/-- Walking one step up the spine.
@isnad1 id=mem.3h4v.s7.86184768f45b from=translated src=- shape=e03430d7 vocab=442e5434
-/
lemma closure_spine_succ {i : ℕ} (hi : i < m)
    (h : ∀ y : Pos, some (Sum.inl (⟨i, hi.le⟩ : SIdx m), y) ∈ T) (y : Pos) :
    some (Sum.inl (⟨i + 1, hi⟩ : SIdx m), y) ∈ T :=
  closure_block T hT _ 0 y (hT _ (h 2) _ (adj_spine hi))

/-- Walking one step down the spine.
@isnad1 id=mem.3h4v.s7.f9d84e10e5bf from=translated src=- shape=baaf51e8 vocab=442e5434
-/
lemma closure_spine_pred {i : ℕ} (hi : i < m)
    (h : ∀ y : Pos, some (Sum.inl (⟨i + 1, hi⟩ : SIdx m), y) ∈ T) (y : Pos) :
    some (Sum.inl (⟨i, hi.le⟩ : SIdx m), y) ∈ T :=
  closure_block T hT _ 2 y (hT _ (h 0) _ (adj_spine hi).symm)

/-- Walking all the way down to spine block `0`.
@isnad1 id=mem.3h4v.s7.9087df37776d from=translated src=- shape=c3096a4b vocab=83ab5719
-/
lemma closure_spine_down : ∀ (i : ℕ) (hi : i ≤ m),
    (∀ y : Pos, some (Sum.inl (⟨i, hi⟩ : SIdx m), y) ∈ T) →
    ∀ y : Pos, some (Sum.inl (⟨0, Nat.zero_le m⟩ : SIdx m), y) ∈ T := by
  intro i
  induction i with
  | zero =>
      intro hi h y
      have : (⟨0, hi⟩ : SIdx m) = ⟨0, Nat.zero_le m⟩ := Subtype.ext rfl
      rw [← this]
      exact h y
  | succ j ih =>
      intro hi h y
      have hj : j < m := hi
      exact ih hj.le (closure_spine_pred T hT hj (fun y => h y)) y

/-- Walking up the spine from block `0`.
@isnad1 id=mem.3h4v.s7.ed1b5140e9ae from=translated src=- shape=bb06994c vocab=83ab5719
-/
lemma closure_spine_up (h0 : ∀ y : Pos, some (Sum.inl (⟨0, Nat.zero_le m⟩ : SIdx m), y) ∈ T) :
    ∀ (i : ℕ) (hi : i ≤ m) (y : Pos), some (Sum.inl (⟨i, hi⟩ : SIdx m), y) ∈ T := by
  intro i
  induction i with
  | zero =>
      intro hi y
      have : (⟨0, hi⟩ : SIdx m) = ⟨0, Nat.zero_le m⟩ := Subtype.ext rfl
      rw [this]
      exact h0 y
  | succ j ih =>
      intro hi y
      have hj : j < m := hi
      exact closure_spine_succ T hT hj (ih hj.le) y

/-- **Connectivity of the hub-free part.**  A set closed under passing from a non-hub
vertex to all of its neighbours, and containing one non-hub vertex, contains all of them.
@isnad1 id=mem.2h4v.s6.ece03d48becf from=translated src=- shape=3e7c1359 vocab=01b75572
-/
theorem closure_all {p₀ : Blk m × Pos} (h₀ : some p₀ ∈ T) :
    ∀ p : Blk m × Pos, some p ∈ T := by
  have hspine0 : ∀ y : Pos, some (Sum.inl (⟨0, Nat.zero_le m⟩ : SIdx m), y) ∈ T := by
    obtain ⟨B, y₀⟩ := p₀
    cases B with
    | inl S =>
        refine closure_spine_down T hT S.1 S.2 (fun y => ?_)
        have : (⟨S.1, S.2⟩ : SIdx m) = S := Subtype.ext rfl
        rw [this]
        exact closure_block T hT _ y₀ y h₀
    | inr L =>
        refine closure_spine_down T hT L.1.1 L.2.1 (fun y => ?_)
        exact closure_leaf_to_spine T hT L (closure_block T hT _ y₀ L.1.2 h₀) y
  have hspine : ∀ (i : ℕ) (hi : i ≤ m) (y : Pos),
      some (Sum.inl (⟨i, hi⟩ : SIdx m), y) ∈ T := closure_spine_up T hT hspine0
  rintro ⟨B, y⟩
  cases B with
  | inl S =>
      have : (⟨S.1, S.2⟩ : SIdx m) = S := Subtype.ext rfl
      rw [← this]
      exact hspine S.1 S.2 y
  | inr L =>
      have hL : (⟨(L.1.1, L.1.2), ⟨L.2.1, L.2.2⟩⟩ : LIdx m) = L := Subtype.ext (by
        ext <;> rfl)
      rw [← hL]
      exact closure_spine_to_leaf T hT ⟨L.1.1, L.2.1⟩ L.1.2 L.2.2
        (fun y => hspine L.1.1 L.2.1 y) y

end Closure

end JSP907
