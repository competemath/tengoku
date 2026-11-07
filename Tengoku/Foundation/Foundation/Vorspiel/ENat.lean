module

public import Tengoku.Seed.Data.ENat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

namespace ENat

open Classical

noncomputable def find (P : ℕ → Prop) : ℕ∞ := if h : ∃ x : ℕ, P x then Nat.find h else ⊤

variable (P : ℕ → Prop)

lemma find_eq_top_iff : find P = ⊤ ↔ ∀ (n : ℕ), ¬P n := by simp [find]

end ENat

end
