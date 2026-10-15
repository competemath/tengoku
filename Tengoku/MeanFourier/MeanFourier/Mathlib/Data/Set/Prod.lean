module

public import Tengoku

public section

attribute [congr] Set.pi_congr

namespace Set
variable {ι : Type*} {α : ι → Type*} {s : Set ι} {t : ∀ i, Set (α i)}

/--
@isnad1 id=iff.0h4v.s5.dc4504512f9d from=translated src=- shape=8552b02a vocab=02537c2a
-/
lemma pi_nonempty : (s.pi t).Nonempty ↔ (∀ i, Nonempty (α i)) ∧ ∀ i ∈ s, (t i).Nonempty := by
  rw [pi_nonempty_iff, ← forall_and]
  congr! with i
  by_cases hi : i ∈ s
  · simpa [hi, ← Set.Nonempty.eq_def] using Set.Nonempty.to_type
  · simp [hi]

end Set
