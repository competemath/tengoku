import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 612, part: a linear function with larger slope eventually wins

Proof plan: Archimedean property (`exists_nat_gt`) for `(b0 - a0) / (a - b)`.
-/

namespace Erdos612

/--
@isnad1 id=not.1h4v.s5.ba854d078f9d from=translated src=- shape=90129337 vocab=3e81b846
-/
theorem linear_escape (a b a0 b0 : ℝ) (hab : b < a) :
    ¬ ∀ p : ℕ, a * p + a0 ≤ b * p + b0 := by
  intro h
  obtain ⟨p, hp⟩ := exists_nat_gt ((b0 - a0) / (a - b))
  have h1 := h p
  have h2 : 0 < a - b := sub_pos.mpr hab
  rw [div_lt_iff₀ h2] at hp
  nlinarith

end Erdos612
