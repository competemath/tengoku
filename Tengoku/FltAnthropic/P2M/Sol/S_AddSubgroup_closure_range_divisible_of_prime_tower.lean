import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddSubgroup_closure_range_divisible_of_prime_tower.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddSubgroup_closure_range_divisible_of_prime_tower

set_option autoImplicit false

namespace RekeyTower

section Tower

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/--
@isnad1 id=ex.2h4v.s7.2991deb53c51 from=translated src=- shape=75b49259 vocab=04a3eabc
-/
theorem tower_exists_smul_eq (p : ℕ) (f : ℕ → M) (htrans : ∀ n, p • f (n + 1) = f n)
    {z : M} (hz : z ∈ AddSubgroup.closure (Set.range f)) :
    ∃ z' ∈ AddSubgroup.closure (Set.range f), p • z' = z := by
  refine AddSubgroup.closure_induction (p := fun z _ =>
      ∃ z' ∈ AddSubgroup.closure (Set.range f), p • z' = z) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨n, rfl⟩
    exact ⟨f (n + 1), AddSubgroup.subset_closure ⟨n + 1, rfl⟩, htrans n⟩
  · exact ⟨0, AddSubgroup.zero_mem _, smul_zero _⟩
  · rintro x y - - ⟨x', hx', rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨x' + y', AddSubgroup.add_mem _ hx' hy', smul_add _ _ _⟩
  · rintro x - ⟨x', hx', rfl⟩
    exact ⟨-x', AddSubgroup.neg_mem _ hx', smul_neg _ _⟩

/--
@isnad1 id=ex.2h5v.s7.14fab28acf53 from=translated src=- shape=5500448c vocab=0345fbe3
-/
theorem tower_exists_pow_smul_eq (p : ℕ) (f : ℕ → M) (htrans : ∀ n, p • f (n + 1) = f n)
    (a : ℕ) {z : M} (hz : z ∈ AddSubgroup.closure (Set.range f)) :
    ∃ z' ∈ AddSubgroup.closure (Set.range f), p ^ a • z' = z := by
  induction a generalizing z with
  | zero => exact ⟨z, hz, by rw [pow_zero, one_smul]⟩
  | succ a ih =>
      obtain ⟨w, hw, rfl⟩ := tower_exists_smul_eq p f htrans hz
      obtain ⟨w', hw', rfl⟩ := ih hw
      exact ⟨w', hw', by rw [pow_succ', mul_smul]⟩

/--
@isnad1 id=ex.2h4v.s7.9a3010b1dcb6 from=translated src=- shape=2445437c vocab=de0ddabb
-/
theorem tower_exists_pow_smul_eq_zero (p : ℕ) (f : ℕ → M) (htors : ∀ n, p ^ n • f n = 0)
    {z : M} (hz : z ∈ AddSubgroup.closure (Set.range f)) : ∃ K : ℕ, p ^ K • z = 0 := by
  refine AddSubgroup.closure_induction (p := fun z _ => ∃ K : ℕ, p ^ K • z = 0) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨n, rfl⟩
    exact ⟨n, htors n⟩
  · exact ⟨0, smul_zero _⟩
  · rintro x y - - ⟨K, hK⟩ ⟨K', hK'⟩
    refine ⟨K + K', ?_⟩
    have hx : p ^ (K + K') • x = 0 := by rw [pow_add, mul_comm, mul_smul, hK, smul_zero]
    have hy : p ^ (K + K') • y = 0 := by rw [pow_add, mul_smul, hK', smul_zero]
    rw [smul_add, hx, hy, add_zero]
  · rintro x - ⟨K, hK⟩
    exact ⟨K, by rw [smul_neg, hK, neg_zero]⟩

/--
@isnad1 id=eq.3h6v.s7.c54a8e939109 from=translated src=- shape=517e15f1 vocab=4762ccc7
-/
theorem tower_smul_eq_zero (f : ℕ → M) (I : Set R) (hkill : ∀ t ∈ I, ∀ n, t • f n = 0)
    {t : R} (ht : t ∈ I) {z : M} (hz : z ∈ AddSubgroup.closure (Set.range f)) : t • z = 0 := by
  refine AddSubgroup.closure_induction (p := fun z _ => t • z = 0) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨n, rfl⟩
    exact hkill t ht n
  · exact smul_zero t
  · rintro x y - - hx hy
    rw [smul_add, hx, hy, add_zero]
  · rintro x - hx
    rw [smul_neg, hx, neg_zero]

/--
@isnad1 id=ex.5h5v.s7.998d8f312fb8 from=translated src=- shape=894f46dc vocab=9d26b196
-/
theorem tower_divisible (p : ℕ) (hp : p.Prime) (f : ℕ → M)
    (htrans : ∀ n, p • f (n + 1) = f n) (htors : ∀ n, p ^ n • f n = 0)
    {z : M} (hz : z ∈ AddSubgroup.closure (Set.range f)) (k : ℕ) (hk : 0 < k) :
    ∃ z' ∈ AddSubgroup.closure (Set.range f), k • z' = z := by

  obtain ⟨a, u, hpu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hp.one_lt.ne'

  obtain ⟨w, hw, rfl⟩ := tower_exists_pow_smul_eq p f htrans a hz

  obtain ⟨K, hK⟩ := tower_exists_pow_smul_eq_zero p f htors hw
  have hcop : Nat.Coprime u (p ^ K) := (hp.coprime_iff_not_dvd.mpr hpu).symm.pow_right K
  by_cases hK0 : p ^ K = 1
  ·
    have hw0 : w = 0 := by rw [← one_smul ℕ w, ← hK0]; exact hK
    refine ⟨0, AddSubgroup.zero_mem _, ?_⟩
    rw [hw0, smul_zero, smul_zero]
  · have h1K : 1 < p ^ K :=
      lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero K hp.ne_zero)) (Ne.symm hK0)
    obtain ⟨v, -, hv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1K
    refine ⟨v • w, AddSubgroup.nsmul_mem _ hw v, ?_⟩

    have huv : (u * v) • w = w := by
      conv_rhs => rw [← one_smul ℕ w]
      rw [← Nat.div_add_mod' (u * v) (p ^ K), hv, add_smul, mul_smul, hK, smul_zero, zero_add]
    rw [mul_smul, ← mul_smul u v w, huv]

/--
@isnad1 id=and.5h5v.s8.c5b2eabd1374 from=translated src=- shape=4e8c669c vocab=0a9bb482
-/
theorem tower_closure_spec (p : ℕ) (hp : p.Prime) (f : ℕ → M)
    (htrans : ∀ n, p • f (n + 1) = f n) (htors : ∀ n, p ^ n • f n = 0)
    (I : Set R) (hkill : ∀ t ∈ I, ∀ n, t • f n = 0) (hne : ∃ n, f n ≠ 0) :
    AddSubgroup.closure (Set.range f) ≠ ⊥ ∧
      (∀ z ∈ AddSubgroup.closure (Set.range f), ∀ k : ℕ, 0 < k →
        ∃ z' ∈ AddSubgroup.closure (Set.range f), k • z' = z) ∧
      (∀ t ∈ I, ∀ z ∈ AddSubgroup.closure (Set.range f), t • z = 0) := by
  refine ⟨?_, fun z hz k hk => tower_divisible p hp f htrans htors hz k hk,
    fun t ht z hz => tower_smul_eq_zero f I hkill ht hz⟩
  obtain ⟨n, hn⟩ := hne
  intro h
  apply hn
  have : f n ∈ AddSubgroup.closure (Set.range f) := AddSubgroup.subset_closure ⟨n, rfl⟩
  rw [h] at this
  exact (AddSubgroup.mem_bot).mp this

end Tower

end RekeyTower

/--
@isnad1 id=and.5h5v.s8.c5b2eabd1374 from=translated src=- shape=4e8c669c vocab=0a9bb482
-/
theorem solution
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : ℕ) (hp : p.Prime) (f : ℕ → M)
    (htrans : ∀ n, p • f (n + 1) = f n) (htors : ∀ n, p ^ n • f n = 0)
    (I : Set R) (hkill : ∀ t ∈ I, ∀ n, t • f n = 0) (hne : ∃ n, f n ≠ 0) :
    AddSubgroup.closure (Set.range f) ≠ ⊥ ∧
      (∀ z ∈ AddSubgroup.closure (Set.range f), ∀ k : ℕ, 0 < k →
        ∃ z' ∈ AddSubgroup.closure (Set.range f), k • z' = z) ∧
      (∀ t ∈ I, ∀ z ∈ AddSubgroup.closure (Set.range f), t • z = 0) :=
  RekeyTower.tower_closure_spec p hp f htrans htors I hkill hne
