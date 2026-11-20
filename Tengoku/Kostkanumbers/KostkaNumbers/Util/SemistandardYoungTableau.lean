/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
This file contains some basic results about SemistandardYoungTableau that I need that are not in
Mathlib. I'll upstream these to Mathlib at some point.
-/

public section

open YoungDiagram

namespace SemistandardYoungTableau

variable {γ : YoungDiagram}

/--
@isnad1 id=eq.1h4v.s5.5e3ae38f1076 from=translated src=- shape=91a5efe1 vocab=ed839512
-/
lemma entry_eq_zero_of_bot (T : SemistandardYoungTableau γ) {i j : ℕ} (h : γ = ⊥) : T i j = 0 :=
  T.zeros <| h ▸ notMem_bot _

/--
@isnad1 id=le.1h4v.s5.7bfd236b9b25 from=translated src=- shape=8df34028 vocab=ff97dd9f
-/
lemma col_le_entry {i j : ℕ} (h : (i, j) ∈ γ) (T : SemistandardYoungTableau γ) : i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    exact lt_of_le_of_lt (ih <| γ.up_left_mem (lt_add_one i).le (by rfl) h)
      <| T.col_strict (lt_add_one i) h

end SemistandardYoungTableau
