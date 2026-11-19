import Tengoku.Erdos278.Erdos278.Uncovered
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Powerset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/yoshiyoyoyo44/erdos278@66ff46ad30c3, `Erdos278/Components.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace Erdos278


open Finset
variable {ι : Type*} [DecidableEq ι]

/--
@isnad1 id=eq.1h4v.s6.5cbcb75b0b9f from=translated src=- shape=74af0bd9 vocab=427bbc7a
-/
theorem sum_powerset_disjoint_union (s t : Finset ι) (hd : Disjoint s t)
    (f : Finset ι → ℚ) :
    ∑ u ∈ (s ∪ t).powerset, f u =
      ∑ u ∈ s.powerset, ∑ v ∈ t.powerset, f (u ∪ v) := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i s hi ih =>
    have hit : i ∉ t := (Finset.disjoint_insert_left.mp hd).1
    have hst : Disjoint s t := (Finset.disjoint_insert_left.mp hd).2
    rw [insert_union, sum_powerset_insert (by simp [hi, hit]),
      sum_powerset_insert hi, ih hst, ih hst]
    simp only [insert_union]

/--
@isnad1 id=coprime.1h4v.s6.9c900ed77604 from=translated src=- shape=5ad6b4a8 vocab=ca8280de
-/
theorem cross_coprime_lcms (s t : Finset ι) (n : ι → ℕ)
    (hc : ∀ i ∈ s, ∀ j ∈ t, (n i).Coprime (n j)) :
    (s.lcm n).Coprime (t.lcm n) := by
  apply Nat.Coprime.of_dvd (s.lcm_dvd_prod n) (t.lcm_dvd_prod n)
  rw [Nat.coprime_prod_left_iff]
  intro i hi
  rw [Nat.coprime_prod_right_iff]
  exact hc i hi

/--
@isnad1 id=iff.1h5v.s6.1743e683a3d6 from=translated src=- shape=32c1a490 vocab=9dc5fe85
-/
theorem clique_union_of_cross_coprime (s t : Finset ι) (n : ι → ℕ) (a : ι → ℤ)
    (hc : ∀ i ∈ s, ∀ j ∈ t, (n i).Coprime (n j)) :
    IsClique n a (s ∪ t) ↔ IsClique n a s ∧ IsClique n a t := by
  constructor
  · intro h
    exact ⟨fun i hi j hj => h i (mem_union_left _ hi) j (mem_union_left _ hj),
      fun i hi j hj => h i (mem_union_right _ hi) j (mem_union_right _ hj)⟩
  · rintro ⟨hs, ht⟩ i hi j hj
    rcases mem_union.mp hi with hi | hi <;> rcases mem_union.mp hj with hj | hj
    · exact hs i hi j hj
    · unfold Compatible
      rw [(hc i hi j hj).gcd_eq_one]
      simp [Int.ModEq]
    · unfold Compatible
      rw [(hc j hj i hi).symm.gcd_eq_one]
      simp [Int.ModEq]
    · exact ht i hi j hj

/--
@isnad1 id=eq.2h5v.s6.ba1c2e610cf7 from=translated src=- shape=07c4022e vocab=b5a819b4
-/
theorem uncoveredTerm_union (s t : Finset ι) (hd : Disjoint s t)
    (n : ι → ℕ) (a : ι → ℤ)
    (hc : ∀ i ∈ s, ∀ j ∈ t, (n i).Coprime (n j)) :
    uncoveredTerm n a (s ∪ t) = uncoveredTerm n a s * uncoveredTerm n a t := by
  have hl : (s ∪ t).lcm n = s.lcm n * t.lcm n := by
    rw [Finset.lcm_union, lcm_eq_nat_lcm, (cross_coprime_lcms s t n hc).lcm_eq_mul]
  have hcl := clique_union_of_cross_coprime s t n a hc
  unfold uncoveredTerm intersectionWeight
  rw [Finset.card_union_of_disjoint hd, hl]
  by_cases hs : IsClique n a s <;> by_cases ht : IsClique n a t
  · have hu := hcl.mpr ⟨hs, ht⟩
    simp [hs, ht, hu, pow_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · have hu : ¬ IsClique n a (s ∪ t) := fun h => ht (hcl.mp h).2
    simp [hs, ht, hu]
  · have hu : ¬ IsClique n a (s ∪ t) := fun h => hs (hcl.mp h).1
    simp [hs, ht, hu]
  · have hu : ¬ IsClique n a (s ∪ t) := fun h => hs (hcl.mp h).1
    simp [hs, ht, hu]

/-- Section 10: uncovered density factors across independent components.
This holds for every choice of residues, before taking the optimum.
@isnad1 id=eq.3h5v.s7.6fcd4cee00b9 from=translated src=- shape=3ccf0aee vocab=d12a797a
-/
theorem uncovered_component_factorization (s t : Finset ι) (hd : Disjoint s t)
    (n : ι → ℕ) (hn : ∀ i ∈ s ∪ t, 0 < n i) (a : ι → ℤ)
    (hc : ∀ i ∈ s, ∀ j ∈ t, (n i).Coprime (n j)) :
    1 - density (s ∪ t) n a = (1 - density s n a) * (1 - density t n a) := by
  rw [uncovered_eq_powerset (s ∪ t) n hn a,
    uncovered_eq_powerset s n (fun i hi => hn i (mem_union_left _ hi)) a,
    uncovered_eq_powerset t n (fun i hi => hn i (mem_union_right _ hi)) a,
    sum_powerset_disjoint_union s t hd, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hus := mem_powerset.mp hu
  have hvt := mem_powerset.mp hv
  exact uncoveredTerm_union u v (hd.mono hus hvt) n a
    (fun i hi j hj => hc i (hus hi) j (hvt hj))

/--
@isnad1 id=and.1h4v.s6.2341861651f0 from=translated src=- shape=5ee1953f vocab=d3907d84
-/
theorem density_bounds (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (a : ι → ℤ) :
    0 ≤ density s n a ∧ density s n a ≤ 1 := by
  have hL : 0 < s.lcm n := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun i hi => (hn i hi).ne'))
  have hLR : (0 : ℚ) < (s.lcm n : ℕ) := by exact_mod_cast hL
  have hsub : coveredFinset s n a ⊆ Finset.Ico 0 (s.lcm n : ℕ) := by
    intro z hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    exact (Finset.mem_filter.mp hi).1
  have hcard : (coveredFinset s n a).card ≤ s.lcm n := by
    simpa using Finset.card_le_card hsub
  constructor
  · exact div_nonneg (by positivity) hLR.le
  · unfold density
    apply (div_le_iff₀ hLR).mpr
    simpa using (show ((coveredFinset s n a).card : ℚ) ≤ (s.lcm n : ℕ) by exact_mod_cast hcard)

/--
@isnad1 id=eq.1h5v.s5.220fe8d55aac from=translated src=- shape=f1ffe706 vocab=d6c3e5d5
-/
theorem density_congr_on (s : Finset ι) (n : ι → ℕ) (a b : ι → ℤ)
    (hab : ∀ i ∈ s, a i = b i) : density s n a = density s n b := by
  have heq : coveredFinset s n a = coveredFinset s n b := by
    unfold coveredFinset
    apply Finset.biUnion_congr rfl
    intro i hi
    rw [hab i hi]
  simp only [density, heq]

/-- Optimal solutions on two independent components can be chosen independently
and glued. Iterating gives the component-product optimum in section 10.
@isnad1 id=ex.5h6v.s7.3d75910f2d84 from=translated src=- shape=02ea410d vocab=32767f5a
-/
theorem component_optima_glue (s t : Finset ι) (hd : Disjoint s t)
    (n : ι → ℕ) (hn : ∀ i ∈ s ∪ t, 0 < n i)
    (hc : ∀ i ∈ s, ∀ j ∈ t, (n i).Coprime (n j))
    (a b : ι → ℤ)
    (ha : ∀ x, density s n x ≤ density s n a)
    (hb : ∀ x, density t n x ≤ density t n b) :
    ∃ x : ι → ℤ,
      (1 - density (s ∪ t) n x = (1 - density s n a) * (1 - density t n b)) ∧
      (∀ y, density (s ∪ t) n y ≤ density (s ∪ t) n x) := by
  classical
  let x : ι → ℤ := fun i => if i ∈ s then a i else b i
  have hxs : density s n x = density s n a :=
    density_congr_on s n x a (fun i hi => by simp [x, hi])
  have hxt : density t n x = density t n b := by
    apply density_congr_on t n x b
    intro i hi
    have his : i ∉ s := fun hs => Finset.disjoint_left.mp hd hs hi
    simp [x, his]
  have heq : 1 - density (s ∪ t) n x = (1 - density s n a) * (1 - density t n b) := by
    rw [uncovered_component_factorization s t hd n hn x hc, hxs, hxt]
  refine ⟨x, heq, fun y => ?_⟩
  have hsa := ha y
  have htb := hb y
  have hsbound := density_bounds s n (fun i hi => hn i (mem_union_left _ hi)) a
  have htbound := density_bounds t n (fun i hi => hn i (mem_union_right _ hi)) b
  have hprod : (1 - density s n a) * (1 - density t n b) ≤
      (1 - density s n y) * (1 - density t n y) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hey := uncovered_component_factorization s t hd n hn y hc
  linarith

end Erdos278
