import Tengoku.Erdos278.Erdos278.Density
import Tengoku.Seed.Data.Nat.GCD.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset
variable {ι : Type*} [DecidableEq ι]

def intersectionWeight (n : ι → ℕ) (a : ι → ℤ) (s : Finset ι) : ℚ :=
  if IsClique n a s then (1 : ℚ) / (s.lcm n : ℕ) else 0

def uncoveredTerm (n : ι → ℕ) (a : ι → ℤ) (s : Finset ι) : ℚ :=
  (-1 : ℚ) ^ s.card * intersectionWeight n a s

/--
@isnad1 id=eq.1h4v.s6.39f9ac360b08 from=translated src=- shape=4768c5cb vocab=cc4c0e85
-/
theorem uncovered_eq_powerset (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (a : ι → ℤ) :
    1 - density s n a = ∑ t ∈ s.powerset, uncoveredTerm n a t := by
  classical
  rw [density_eq_graphValue s n hn a]
  have hsplit := Finset.sum_filter_add_sum_filter_not s.powerset
    (fun t => t.Nonempty) (uncoveredTerm n a)
  have he : ∑ t ∈ s.powerset with ¬ t.Nonempty, uncoveredTerm n a t = 1 := by
    have hfilter : s.powerset.filter (fun t => ¬t.Nonempty) = {∅} := by
      ext t
      simp only [mem_filter, mem_powerset, mem_singleton, not_nonempty_iff_eq_empty]
      exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact empty_subset _, h⟩⟩
    rw [hfilter, sum_singleton]
    have hcl : IsClique n a ∅ := by simp [IsClique]
    simp [uncoveredTerm, intersectionWeight, hcl]
  rw [he] at hsplit
  have hmain : graphValue s n (Compatible n a) =
      - ∑ t ∈ s.powerset with t.Nonempty, uncoveredTerm n a t := by
    unfold graphValue
    rw [← Finset.sum_coe_sort (s.powerset.filter (·.Nonempty)) (uncoveredTerm n a),
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    unfold uncoveredTerm intersectionWeight
    by_cases hc : IsClique n a t.1
    · rw [ite_eq_left hc]
      have hc' : ∀ i ∈ t.1, ∀ j ∈ t.1, Compatible n a i j := hc
      rw [ite_eq_left hc']
      simp [pow_succ, div_eq_mul_inv]
    · rw [ite_eq_right hc]
      have hc' : ¬(∀ i ∈ t.1, ∀ j ∈ t.1, Compatible n a i j) := hc
      rw [ite_eq_right hc']
      simp
  rw [hmain]
  linarith

/-- The independent/coprime special case, including the empty family.
@isnad1 id=eq.2h4v.s7.11744ecf58f8 from=translated src=- shape=c0714beb vocab=61f2beb1
-/
theorem coprime_uncovered_product (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (a : ι → ℤ)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (n i).Coprime (n j)) :
    1 - density s n a = ∏ i ∈ s, (1 - (1 : ℚ) / n i) := by
  rw [uncovered_eq_powerset s n hn a, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t ht
  have hts := mem_powerset.mp ht
  have hcl : IsClique n a t := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j; exact Int.ModEq.refl _
    · unfold Compatible
      rw [(hc i (hts hi) j (hts hj) hij).gcd_eq_one]
      simp [Int.ModEq]
  have hprod : t.lcm n = t.prod n :=
    Finset.lcm_eq_prod (fun i hi j hj hij => hc i (hts hi) j (hts hj) hij)
  simp [uncoveredTerm, intersectionWeight, ite_eq_left hcl, hprod]

end Erdos278
