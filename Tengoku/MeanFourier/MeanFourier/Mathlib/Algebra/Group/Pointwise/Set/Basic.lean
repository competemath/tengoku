module

public import Tengoku

open scoped Pointwise

public section

namespace Set
variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

/--
@isnad1 id=eq.0h5v.s7.8bd390ff93da from=translated src=- shape=0f3809a5 vocab=9fe352e8
-/
@[to_additive]
lemma pi_mul (s : Set ι) (t u : ∀ i, Set (M i)) : s.pi (fun i ↦ t i * u i) = s.pi t * s.pi u := by
  classical
  ext x
  simp only [mem_pi, mem_mul]
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose! y hy z hz hyz using h
    exact ⟨fun i ↦ if i ∈ s then y i else x i, by simpa +contextual,
      fun i ↦ if i ∈ s then z i else 1, by simpa +contextual, by ext; dsimp; grind⟩
  · rintro ⟨y, hy, z, hz, rfl⟩ i hi
    exact ⟨y i, hy _ hi, z i, hz _ hi, rfl⟩

/--
@isnad1 id=eq.1h5v.s7.df7e09c809df from=translated src=- shape=bbc4c739 vocab=d9966019
-/
@[to_additive nsmul_pi]
lemma pi_pow (s : Set ι) (t : ∀ i, Set (M i)) :
    ∀ {n : ℕ}, n ≠ 0 → s.pi t ^ n = s.pi (fun i ↦ t i ^ n)
  | 1, _ => by simp
  | n + 2, _ => by simp [pow_succ _ (n + 1), pi_mul, ← pi_pow]

/--
@isnad1 id=eq.0h4v.s7.e901e7de3ad2 from=translated src=- shape=6049d865 vocab=788e7a86
-/
@[to_additive nsmul_univ_pi]
lemma univ_pi_pow (t : ∀ i, Set (M i)) : ∀ n : ℕ, univ.pi t ^ n = univ.pi (fun i ↦ t i ^ n)
  | 0 => by simp [← Set.singleton_one, ← Set.univ_pi_singleton]
  | n + 1 => by simp [pi_pow]

end Set

namespace Set
variable {α M : Type*} [Monoid M] {f g : α → M}

-- TODO: How to most efficiently `to_fun` this?
/--
@isnad1 id=le.0h4v.s6.37e608df623f from=translated src=- shape=3b8750b6 vocab=2098d52d
-/
@[to_additive]
lemma range_mul_subset : range (f * g) ⊆ range f * range g := by
  simp [range_subset_iff, Set.mul_mem_mul]

end Set
