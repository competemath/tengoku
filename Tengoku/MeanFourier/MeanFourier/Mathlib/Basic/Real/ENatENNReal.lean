module

public import Tengoku

public section

namespace ENat
variable {n : ℕ∞}

/--
@isnad1 id=iff.0h2v.s4.a24590abb996 from=translated src=- shape=1abd8023 vocab=bf4a14be
-/
@[simp] lemma toENNReal_le_natCast {m : ℕ∞} {n : ℕ} : toENNReal m ≤ n ↔ m ≤ n := by
  rw [← ENat.toENNReal_le]; rfl

end ENat
