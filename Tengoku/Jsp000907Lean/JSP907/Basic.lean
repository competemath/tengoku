/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Tengoku.Jsp000907Lean.JSP907.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic adjacency lemmas for `JSP907.G`
-/

namespace JSP907

variable {m : ℕ}

/-- Pentagon edges.
@isnad1 id=adj.1h4v.s5.acdc3dfc59b5 from=translated src=- shape=d03f7ad0 vocab=8a0ec845
-/
lemma adj_block (B : Blk m) {y z : Pos} (h : PosAdj y z) :
    (G m).Adj (some (B, y)) (some (B, z)) := Or.inl ⟨rfl, h⟩

/-- The hub is adjacent to every non-attachment vertex of every leaf block.
@isnad1 id=adj.1h3v.s6.911ec1af166b from=translated src=- shape=8d61c44c vocab=70673b63
-/
lemma adj_hub (L : LIdx m) {y : Pos} (h : y ≠ L.1.2) :
    (G m).Adj none (some (Sum.inr L, y)) := by
  change ext (Sum.inr L, y) = none
  rw [ext_inr, extL, ite_eq_right h]

/-- The attachment edge between a spine block and the leaf block hanging from it.
@isnad1 id=adj.1h3v.s7.6a84370fc551 from=translated src=- shape=2f3df957 vocab=b9f5cc7f
-/
lemma adj_attach (S : SIdx m) {x : Pos} (h : LeafOK m S.1 x) :
    (G m).Adj (some (Sum.inl S, x)) (some (Sum.inr ⟨(S.1, x), ⟨S.2, h⟩⟩, x)) := by
  refine Or.inr (Or.inl ?_)
  rw [ext_inl, extS, dite_eq_left h]

/-- The spine edge `(i, 2) — (i+1, 0)`, available whenever `i < m`.
@isnad1 id=adj.1h2v.s6.dc8266b11037 from=translated src=- shape=bc46b9fd vocab=29c0ccd9
-/
lemma adj_spine {i : ℕ} (hi : i < m) :
    (G m).Adj (some (Sum.inl ⟨i, hi.le⟩, 2)) (some (Sum.inl ⟨i + 1, hi⟩, 0)) := by
  refine Or.inr (Or.inl ?_)
  have hL : ¬ LeafOK m i 2 := by
    simp only [LeafOK, not_or]
    refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · rintro ⟨h, -⟩; exact absurd h (by decide)
    · rintro ⟨-, h⟩; omega
  rw [ext_inl, extS, dite_eq_right hL, ite_eq_right (by decide : ¬ (2 : Pos) = 0)]
  have : min (i + 1) m = i + 1 := by omega
  simp [this]

/--
@isnad1 id=leafok.1h3v.s5.aeebc353d868 from=translated src=- shape=70cefa2b vocab=085a74f8
-/
lemma leafOK_of_mem {i : ℕ} {y : Pos} (h : y = 1 ∨ y = 3 ∨ y = 4) : LeafOK m i y := by
  rcases h with h | h | h <;> simp [LeafOK, h]

/--
@isnad1 id=leafok.1h2v.s4.e1112c20cb6d from=translated src=- shape=4cbd4288 vocab=085a74f8
-/
lemma leafOK_zero {i : ℕ} (h : i = 0) : LeafOK m i 0 := by
  simp [LeafOK, h]

/--
@isnad1 id=leafok.1h2v.s4.4f5accfcb490 from=translated src=- shape=e8491207 vocab=085a74f8
-/
lemma leafOK_last {i : ℕ} (h : i = m) : LeafOK m i 2 := by
  simp [LeafOK, h]

/--
@isnad1 id=or.1h1v.s6.01027ede473c from=translated src=- shape=ef8f28f0 vocab=460b7355
-/
lemma pos_ne_two {y : Pos} (h : y ≠ 2) : y = 0 ∨ y = 1 ∨ y = 3 ∨ y = 4 := by
  revert y; decide

/--
@isnad1 id=or.1h1v.s6.b0aed387ef7b from=translated src=- shape=ef8f28f0 vocab=460b7355
-/
lemma pos_ne_zero {y : Pos} (h : y ≠ 0) : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by
  revert y; decide

set_option maxRecDepth 8000 in
/-- Forcing inside a pentagon: in a proper `3`-colouring of the pentagon, if four of the
five slots avoid the colour `α`, the fifth slot has colour `α`.
@isnad1 id=eq.2h3v.s6.5b7bd9fac2e0 from=translated src=- shape=58bde739 vocab=ec8ed9d5
-/
lemma pentagon_forcing (C : Pos → Fin 3) (α : Fin 3) (z : Pos)
    (hC : ∀ y y', PosAdj y y' → C y ≠ C y') (h : ∀ y, y ≠ z → C y ≠ α) :
    C z = α := by
  revert C α z
  decide +kernel

end JSP907
