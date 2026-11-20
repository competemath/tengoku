/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Tengoku
import Tengoku.Kostkanumbers.KostkaNumbers.Util.Diagrams

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

public section

/-!
This shows that YoungDiagrams are equivalent to finitely supported antitone functions from ℕ to ℕ.
-/

open YoungDiagram

namespace YoungDiagram

def rowLen' (γ : YoungDiagram) : ℕ →₀ ℕ := ⟨Finset.range (γ.colLen 0),
  γ.rowLen, by simp [← Nat.pos_iff_ne_zero, ← mem_iff_lt_colLen, mem_iff_lt_rowLen]⟩

lemma rowLen'_anti (γ : YoungDiagram) : Antitone γ.rowLen' := by
  rw [Finsupp.coe_mk]
  exact γ.rowLen_anti

lemma rowLen'_eq_rowLen {γ : YoungDiagram} {i : ℕ} : γ.rowLen' i = γ.rowLen i := by
  simp [rowLen']

@[simp] lemma rowLen'_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen' i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  push Not at hi
  exact hi

lemma rowLen'_eq_zero_of_ge_length {γ : YoungDiagram} (i : ℕ) (hi : i ≥ γ.rowLens.length) :
    γ.rowLen' i = 0 := by
  rw [length_rowLens] at hi
  exact rowLen'_eq_zero (by lia)

@[simp]
lemma rowLen'_bot : (⊥ : YoungDiagram).rowLen' = 0 := by
  ext
  simp [rowLen']

end YoungDiagram
