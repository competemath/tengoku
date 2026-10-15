module

public import Tengoku

open scoped Pointwise

public section

namespace Set
variable {G X : Type*} [Group G] [MulAction G X] {s : Set G} {t : Set X} {x : X}

/--
@isnad1 id=iff.0h5v.s6.4dbb12c1c24c from=translated src=- shape=ff482ee3 vocab=009cca2d
-/
@[to_additive]
lemma mem_smul_iff_inv_smul_mem : x ∈ s • t ↔ ∃ a ∈ s, a⁻¹ • x ∈ t where
  mp := by rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, by rwa [inv_smul_smul]⟩
  mpr := by rintro ⟨a, ha, hb⟩; exact ⟨a, ha, a⁻¹ • x, hb, smul_inv_smul ..⟩

end Set
