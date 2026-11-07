module

public import Tengoku.Seed.Data.ENat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

namespace ENat

open Classical

noncomputable def find (P : ℕ → Prop) : ℕ∞ := if h : ∃ x : ℕ, P x then Nat.find h else ⊤

variable (P : ℕ → Prop)

/--
@isnad1 id=iff.0h1v.s4.f1b7f6b52c4f from=translated src=- shape=6ab95e14 vocab=c69da6d7
-/
lemma find_eq_top_iff : find P = ⊤ ↔ ∀ (n : ℕ), ¬P n := by simp [find]

end ENat

end
