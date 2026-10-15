/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Tengoku

/-!
# LeanPool.LeanPolyABC.Lib.Radical
-/

@[expose] public section

noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace LeanPolyABC

variable {k : Type*} [Field k] [DecidableEq k]
variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α] [UniqueFactorizationMonoid α]

open scoped Classical in
/-- Prime factors of `a` are monic factors of `a` without duplication. -/
def primeFactors (a : α) : Finset α :=
  (normalizedFactors a).toFinset

open scoped Classical in
/-- Radical of `a` is a product of prime factors of `a`. -/
def radical (a : α) : α :=
  (primeFactors a).prod id

/--
@isnad1 id=eq.0h1v.s5.c16d76229829 from=translated src=- shape=07c517b0 vocab=ec345078
-/
theorem radical_zero_eq_one : radical (0 : α) = 1 := by
  classical
  rw [radical, primeFactors, normalizedFactors_zero, Multiset.toFinset_zero, Finset.prod_empty]

/--
@isnad1 id=eq.0h1v.s5.1eda13020f63 from=translated src=- shape=07c517b0 vocab=ec345078
-/
theorem radical_one_eq_one : radical (1 : α) = 1 := by
  classical
  rw [radical, primeFactors, normalizedFactors_one, Multiset.toFinset_zero, Finset.prod_empty]

/--
@isnad1 id=eq.1h3v.s5.1ae2fdfa802e from=translated src=- shape=f04fb5af vocab=c5f3601a
-/
theorem radical_associated_eq {a b : α} (h : Associated a b) : radical a = radical b := by
  classical
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · rfl
  · simp_rw [radical, primeFactors]
    rw [(associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mp h]

/--
@isnad1 id=eq.1h2v.s5.b301a59f847f from=translated src=- shape=aee97021 vocab=cb4fb6a2
-/
theorem radical_unit_eq_one {a : α} (h : IsUnit a) : radical a = 1 :=
  (radical_associated_eq (associated_one_iff_isUnit.mpr h)).trans radical_one_eq_one

/--
@isnad1 id=eq.1h3v.s5.5289be75f3f0 from=translated src=- shape=634ad572 vocab=63261c3c
-/
theorem radical_mul_unit_left {u a : α} (h : IsUnit u) : radical (u * a) = radical a :=
  radical_associated_eq (associated_unit_mul_left _ _ h)

/--
@isnad1 id=eq.1h3v.s5.7ffc9e6d0939 from=translated src=- shape=9a9156b7 vocab=63261c3c
-/
theorem radical_mul_unit_right {u a : α} (h : IsUnit u) : radical (a * u) = radical a :=
  radical_associated_eq (associated_mul_unit_left _ _ h)

/--
@isnad1 id=eq.1h3v.s5.74c68b39eb71 from=translated src=- shape=0920a205 vocab=6020f57b
-/
theorem primeFactors_pow (a : α) {n : ℕ} (hn : 0 < n) : primeFactors (a ^ n) = primeFactors a := by
  classical
  simp_rw [primeFactors]
  simp only [normalizedFactors_pow]
  rw [Multiset.toFinset_nsmul _ _ (ne_of_gt hn)]

/--
@isnad1 id=eq.1h3v.s5.98678527122d from=translated src=- shape=c28e2e1a vocab=4b0f69ac
-/
theorem radical_pow (a : α) {n : Nat} (hn : 0 < n) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]

/--
@isnad1 id=dvd.0h2v.s5.8b09711062bc from=translated src=- shape=441b688c vocab=fbe39d42
-/
theorem radical_dvd_self (a : α) : radical a ∣ a := by
  classical
  by_cases ha : a = 0
  · simp_all
  · rw [radical, ← Finset.prod_val, ← (prod_normalizedFactors ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors, Multiset.toFinset_val]
    apply Multiset.dedup_le

/--
@isnad1 id=dvd.1h3v.s6.2bee276335a1 from=translated src=- shape=6775b84d vocab=7479611c
-/
theorem radical_dvd_radical_self_mul {a b : α} (hb : b ≠ 0) : radical a ∣ radical (a * b) := by
  classical
  by_cases ha : a = 0
  · rw [ha, zero_mul]
  · rw [radical, ← Finset.prod_val, radical, ← Finset.prod_val]
    apply Multiset.prod_dvd_prod_of_le
    repeat rw [primeFactors]
    rw [normalizedFactors_mul ha hb, Finset.val_le_iff, Multiset.toFinset_add]
    exact Finset.subset_union_left

/--
@isnad1 id=dvd.1h3v.s6.837ee3abf7f3 from=translated src=- shape=9ec0914d vocab=7479611c
-/
theorem radical_dvd_radical_mul_self {a b : α} (hb : b ≠ 0) : radical a ∣ radical (b * a) := by
  rw [mul_comm b a]
  exact radical_dvd_radical_self_mul hb

/--
@isnad1 id=dvd.2h3v.s6.7ab33b4d0f29 from=translated src=- shape=1a997406 vocab=fbe39d42
-/
theorem radical_dvd_radical_of_dvd {a b : α} (hb : b ≠ 0) (h : a ∣ b) :
    radical a ∣ radical b := by
  rcases h with ⟨c, hc⟩
  rw [hc]
  rw [hc, mul_ne_zero_iff] at hb
  exact radical_dvd_radical_self_mul hb.right

/--
@isnad1 id=dvd.0h3v.s6.de67a589d63b from=translated src=- shape=41e3bdd8 vocab=7479611c
-/
theorem radical_mul_dvd_mul_radical (a b : α) : radical (a * b) ∣ radical a * radical b := by
  classical
  by_cases ha : a = 0
  · simp_all
  by_cases hb : b = 0
  · simp_all
  rw [radical, primeFactors, normalizedFactors_mul ha hb, Multiset.toFinset_add, radical,
    primeFactors, radical, primeFactors]
  exact ⟨((normalizedFactors a).toFinset ∩ (normalizedFactors b).toFinset).prod id,
    (Finset.prod_union_inter).symm⟩

/--
@isnad1 id=eq.1h2v.s5.e6ba43f6f2e7 from=translated src=- shape=d668b3d7 vocab=879931f1
-/
theorem radical_prime {a : α} (ha : Prime a) : radical a = normalize a := by
  classical
  rw [radical, primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

/--
@isnad1 id=eq.2h3v.s6.72b4e0222b8f from=translated src=- shape=ea2e9c56 vocab=223f9c44
-/
theorem radical_prime_pow {a : α} (ha : Prime a) {n : ℕ} (hn : 1 ≤ n) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_prime ha

/--
@isnad1 id=iff.2h3v.s6.d4d592b9f175 from=translated src=- shape=f6d47ec9 vocab=42509f19
-/
theorem prime_dvd_radical_iff {a p : α} (ha : a ≠ 0) (hp : Prime p) :
    p ∣ radical a ↔ p ∣ a := by
  classical
  constructor
  · exact fun h => h.trans <| radical_dvd_self a
  · intro hpa
    rcases exists_mem_normalizedFactors_of_dvd ha hp.irreducible hpa with ⟨q, ⟨hqf, hpq⟩⟩
    rw [hpq.dvd_iff_dvd_left, radical, primeFactors]
    exact Finset.dvd_prod_of_mem id (Multiset.mem_toFinset.mpr hqf)

/--
@isnad1 id=iff.1h2v.s5.f47f8c7a0084 from=translated src=- shape=70140aaa vocab=cb4fb6a2
-/
theorem radical_isUnit_iff {a : α} (h : a ≠ 0) : IsUnit (radical a) ↔ IsUnit a := by
  constructor
  · contrapose
    intro ha
    rcases exists_mem_factors h ha with ⟨p, hpf⟩
    have hpp := prime_of_factor _ hpf
    have hpd := dvd_of_mem_factors hpf
    exact not_isUnit_of_not_isUnit_dvd hpp.not_isUnit ((prime_dvd_radical_iff h hpp).mpr hpd)
  · intro ha
    rw [radical_unit_eq_one ha]
    exact isUnit_one

-- Theorems for commutative rings
variable {R : Type _} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R]

namespace IsCoprime

omit [IsDomain R] in
/-- coprime polynomials have disjoint prime factors (as multisets). -/
private theorem disjoint_normalizedFactors {a b : R} (hc : IsCoprime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) := by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  have xp := prime_of_normalized_factor x hxa
  exact xp.not_isUnit (hc.isUnit_of_dvd' x_dvd_a x_dvd_b)

omit [IsDomain R] in
-- coprime polynomials have disjoint prime factors (as finsets)
private theorem disjoint_primeFactors {a b : R} (hc : IsCoprime a b) :
    Disjoint (primeFactors a) (primeFactors b) := by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)

omit [IsDomain R] in
private theorem hMul_primeFactors_disjUnion {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsCoprime a b) :
    primeFactors (a * b) =
      (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) := by
  classical
  rw [Finset.disjUnion_eq_union]
  simp_rw [primeFactors]
  rw [normalizedFactors_mul ha hb, Multiset.toFinset_add]

end IsCoprime

omit [IsDomain R] in
-- possible TODO: the proof is unnecessarily long
/--
@isnad1 id=eq.0h1v.s6.16aa62b13153 from=translated src=- shape=8b7f55f4 vocab=cec52790
-/
@[simp]
theorem radical_neg_one : radical (-1 : R) = 1 :=
  radical_unit_eq_one isUnit_one.neg

omit [IsDomain R] in
/--
@isnad1 id=eq.1h3v.s6.90de1044507c from=translated src=- shape=c67a405c vocab=3b1ec984
-/
theorem radical_hMul {a b : R} (hc : IsCoprime a b) :
    radical (a * b) = radical a * radical b := by
  classical
  by_cases ha : a = 0
  · subst ha; rw [isCoprime_zero_left] at hc
    simp only [MulZeroClass.zero_mul, radical_zero_eq_one, one_mul, radical_unit_eq_one hc]
  by_cases hb : b = 0
  · subst hb; rw [isCoprime_zero_right] at hc
    simp only [MulZeroClass.mul_zero, radical_zero_eq_one, mul_one, radical_unit_eq_one hc]
  simp_rw [radical]
  rw [IsCoprime.hMul_primeFactors_disjUnion ha hb hc]
  rw [Finset.prod_disjUnion (IsCoprime.disjoint_primeFactors hc)]

omit [IsDomain R] in
/--
@isnad1 id=eq.0h2v.s6.913bfae8d775 from=translated src=- shape=4993d383 vocab=cec52790
-/
theorem radical_neg {a : R} : radical (-a) = radical a :=
  neg_one_mul a ▸ (radical_associated_eq <| associated_unit_mul_left a (-1) isUnit_one.neg)

-- This actually holds for nontrivial monoids - do not need ring assumption.
/--
@isnad1 id=ne.0h2v.s5.419754d11e1b from=translated src=- shape=33a1e92b vocab=bf7c9dd6
-/
theorem radical_ne_zero (a : R) : radical a ≠ 0 := by
  classical
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_notMem_normalizedFactors _

namespace Polynomial

/--
@isnad1 id=le.1h2v.s7.83cf090cc929 from=translated src=- shape=103ce0a4 vocab=91388f7b
-/
theorem radical_degree_le {a : k[X]} (ha : a ≠ 0) : (radical a).degree ≤ a.degree :=
  degree_le_of_dvd (radical_dvd_self a) ha

/--
@isnad1 id=le.0h2v.s6.081c33e038ac from=translated src=- shape=1f1420c5 vocab=8e7cc28a
-/
theorem radical_natDegree_le (a : k[X]) : (radical a).natDegree ≤ a.natDegree := by
  by_cases ha : a = 0
  · rw [ha, radical_zero_eq_one, natDegree_one, natDegree_zero]
  · exact natDegree_le_of_dvd (radical_dvd_self a) ha

/--
@isnad1 id=le.0h3v.s8.d83442d2cb61 from=translated src=- shape=b06e1234 vocab=f888e5cb
-/
theorem radical_natDegree_mul_le (a b : k[X]) :
    (radical (a * b)).natDegree ≤ (radical a).natDegree + (radical b).natDegree := by
  rw [← natDegree_mul (radical_ne_zero _) (radical_ne_zero _)]
  exact natDegree_le_of_dvd (radical_mul_dvd_mul_radical a b)
    (mul_ne_zero (radical_ne_zero _) (radical_ne_zero _))

end Polynomial

end LeanPolyABC
