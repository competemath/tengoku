module

public import Tengoku

public section

namespace ENat
variable {a b n : ℕ∞}

/--
@isnad1 id=iff.0h2v.s5.32170e790b52 from=translated src=- shape=c0f4b419 vocab=df286c23
-/
lemma mul_eq_top : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := WithTop.mul_eq_top_iff

/--
@isnad1 id=iff.0h1v.s4.1792c7eef636 from=translated src=- shape=c58f4174 vocab=6102b851
-/
@[simp] lemma le_toNat_self_iff : n ≤ n.toNat ↔ n ≠ ⊤ where
  mp := by rintro hn rfl; simp at hn
  mpr hn := by rw [natCast_toNat hn]

end ENat
