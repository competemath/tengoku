module

public import Tengoku

public section

open scoped Pointwise

namespace Set
variable {α : Type*} [Group α]

/--
@isnad1 id=iff.0h4v.s6.6384e1cf98f5 from=translated src=- shape=dcbf8701 vocab=4bc7c5f9
-/
@[to_additive (attr := simp)]
lemma mul_mem_smul_set_iff (a : α) {b : α} {s : Set α} : a * b ∈ a • s ↔ b ∈ s :=
  smul_mem_smul_set_iff

end Set
