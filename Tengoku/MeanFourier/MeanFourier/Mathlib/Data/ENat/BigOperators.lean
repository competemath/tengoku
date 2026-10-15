module

public import Tengoku

public section

namespace ENat
variable {ι : Type*} {s : Finset ι} {f : ι → ℕ∞}

/--
@isnad1 id=iff.0h3v.s6.7cad6e5f79ea from=translated src=- shape=d6f4db68 vocab=7b6aa473
-/
@[simp] lemma prod_eq_top : ∏ i ∈ s, f i = ⊤ ↔ (∃ i ∈ s, f i = ⊤) ∧ ∀ i ∈ s, f i ≠ 0 :=
  WithTop.prod_eq_top_iff

end ENat
