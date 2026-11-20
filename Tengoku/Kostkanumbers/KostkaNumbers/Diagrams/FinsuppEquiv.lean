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

/--
@isnad1 id=antitone.0h1v.s4.564478880b58 from=translated src=- shape=0657c12c vocab=2e7074e7
-/
lemma rowLen'_anti (γ : YoungDiagram) : Antitone γ.rowLen' := by
  rw [Finsupp.coe_mk]
  exact γ.rowLen_anti

/--
@isnad1 id=eq.0h2v.s4.c6fdddedc9b1 from=translated src=- shape=adfa6799 vocab=58f2db77
-/
lemma rowLen'_eq_rowLen {γ : YoungDiagram} {i : ℕ} : γ.rowLen' i = γ.rowLen i := by
  simp [rowLen']

/--
@isnad1 id=eq.1h2v.s5.b3c18f7982d1 from=translated src=- shape=0bd7c4c7 vocab=0e376087
-/
@[simp] lemma rowLen'_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen' i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  push Not at hi
  exact hi

/--
@isnad1 id=eq.1h2v.s5.21683f19cba8 from=translated src=- shape=efb850ec vocab=83f12dd3
-/
lemma rowLen'_eq_zero_of_ge_length {γ : YoungDiagram} (i : ℕ) (hi : i ≥ γ.rowLens.length) :
    γ.rowLen' i = 0 := by
  rw [length_rowLens] at hi
  exact rowLen'_eq_zero (by lia)

/--
@isnad1 id=eq.0h0v.s5.b9c78d758a90 from=translated src=- shape=6e9d2abb vocab=b39afd80
-/
@[simp]
lemma rowLen'_bot : (⊥ : YoungDiagram).rowLen' = 0 := by
  ext
  simp [rowLen']

end YoungDiagram
