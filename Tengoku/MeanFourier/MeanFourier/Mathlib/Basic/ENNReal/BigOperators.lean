module

public import Tengoku

public section

namespace ENNReal
variable {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞}

/--
@isnad1 id=iff.0h3v.s6.595dab6a9df9 from=translated src=- shape=d6f4db68 vocab=d13fe371
-/
@[simp] lemma prod_eq_top : ∏ i ∈ s, f i = ⊤ ↔ (∃ i ∈ s, f i = ⊤) ∧ ∀ i ∈ s, f i ≠ 0 :=
  WithTop.prod_eq_top_iff

end ENNReal
