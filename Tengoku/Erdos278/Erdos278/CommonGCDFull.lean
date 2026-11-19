import Tengoku.Erdos278.Erdos278.CommonGCD
import Tengoku.Erdos278.Erdos278.Uncovered

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/yoshiyoyoyo44/erdos278@66ff46ad30c3, `Erdos278/CommonGCDFull.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace Erdos278


open Finset
variable {ι : Type*} [DecidableEq ι]

theorem lcm_scale_nonempty (s : Finset ι) (hs : s.Nonempty)
    (g : ℕ) (b : ι → ℕ) :
    s.lcm (fun i => g * b i) = g * s.lcm b := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    by_cases hne : s.Nonempty
    · rw [Finset.lcm_insert, Finset.lcm_insert, ih hne]
      exact Nat.lcm_mul_left g (b i) (s.lcm b)
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      simp

theorem common_gcd_compatible_iff (g : ℕ) (b : ι → ℕ)
    (hc : ∀ i j, i ≠ j → (b i).Coprime (b j))
    (part : ι → Fin g) (i j : ι) :
    Compatible (fun k => g * b k) (fun k => (part k : ℤ)) i j ↔
      part i = part j := by
  by_cases hij : i = j
  · subst j; simp [Compatible]
  · unfold Compatible
    rw [Nat.gcd_mul_left, (hc i j hij).gcd_eq_one, mul_one,
      Int.natCast_modEq_iff]
    change (part i).val % g = (part j).val % g ↔ part i = part j
    rw [Nat.mod_eq_of_lt (part i).isLt, Nat.mod_eq_of_lt (part j).isLt]
    exact Fin.ext_iff.symm

theorem sum_monochromatic_nonempty {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset ι) (hs : s.Nonempty) (part : ι → κ) :
    (∑ t : κ, if (∀ i ∈ s, part i = t) then (1 : ℚ) else 0) =
      if (∀ i ∈ s, ∀ j ∈ s, part i = part j) then 1 else 0 := by
  classical
  obtain ⟨i, hi⟩ := hs
  rw [Finset.sum_eq_single (part i)]
  · have he : (∀ j ∈ s, part j = part i) ↔
        (∀ j ∈ s, ∀ k ∈ s, part j = part k) := by
      exact ⟨fun h j hj k hk => (h j hj).trans (h k hk).symm,
        fun h j hj => h j hj i hi⟩
    simp only [he]
  · intro t _ ht
    have h : ¬ (∀ j ∈ s, part j = t) := fun h => ht (h i hi).symm
    simp [h]
  · simp

theorem fiber_product_expansion {κ : Type*} [DecidableEq κ]
    (s : Finset ι) (b : ι → ℕ) (part : ι → κ) (t : κ) :
    (∏ i ∈ s with part i = t, (1 - (1 : ℚ) / b i)) =
      ∑ u ∈ s.powerset,
        if (∀ i ∈ u, part i = t) then (-1 : ℚ) ^ u.card / (u.prod b : ℕ) else 0 := by
  classical
  have hp : (s.filter (fun i => part i = t)).powerset =
      s.powerset.filter (fun u => ∀ i ∈ u, part i = t) := by
    ext u
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨fun i hi => (mem_filter.mp (h hi)).1,
      fun i hi => (mem_filter.mp (h hi)).2⟩,
      fun h i hi => mem_filter.mpr ⟨h.1 hi, h.2 i hi⟩⟩
  rw [Finset.prod_sub, hp, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  simp [div_eq_mul_inv]

/-- The full fiber product formula of section 11, for every residue assignment
to the g labeled parts. Neither g nor the factors have to be prime.-/
theorem common_gcd_uncovered_formula (s : Finset ι) (g : ℕ) (hg : 0 < g)
    (b : ι → ℕ) (hb : ∀ i ∈ s, 0 < b i)
    (hc : ∀ i j, i ≠ j → (b i).Coprime (b j)) (part : ι → Fin g) :
    1 - density s (fun i => g * b i) (fun i => (part i : ℤ)) =
      (∑ t : Fin g, ∏ i ∈ s with part i = t, (1 - (1 : ℚ) / b i)) / g := by
  classical
  have hgQ : (g : ℚ) ≠ 0 := by positivity
  rw [uncovered_eq_powerset s (fun i => g * b i)
    (fun i hi => Nat.mul_pos hg (hb i hi))]
  simp_rw [fiber_product_expansion]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases he : u = ∅
  · subst u
    simp [uncoveredTerm, intersectionWeight, IsClique, hgQ]
  · have hne : u.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    have hl : u.lcm (fun i => g * b i) = g * u.prod b := by
      rw [lcm_scale_nonempty u hne, Finset.lcm_eq_prod
        (fun i _ j _ hij => hc i j hij)]
    have hcolor : (∀ i ∈ u, ∀ j ∈ u, part i = part j) ↔
        IsClique (fun i => g * b i) (fun i => (part i : ℤ)) u := by
      simp only [IsClique, common_gcd_compatible_iff g b hc part]
    have hsum : (∑ t : Fin g, if (∀ i ∈ u, part i = t)
          then (-1 : ℚ) ^ u.card / (u.prod b : ℕ) else 0) =
        (∑ t : Fin g, if (∀ i ∈ u, part i = t) then (1 : ℚ) else 0) *
          ((-1 : ℚ) ^ u.card / (u.prod b : ℕ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : ∀ i ∈ u, part i = t <;> simp [h]
    rw [hsum, sum_monochromatic_nonempty u hne part]
    simp only [hcolor]
    unfold uncoveredTerm intersectionWeight
    by_cases hcl : IsClique (fun i => g * b i) (fun i => (part i : ℤ)) u
    · simp [hcl, hl, div_eq_mul_inv, mul_comm, mul_left_comm]
    · simp [hcl]

variable [Fintype ι]

/-- The explicitly displayed partition objective, including empty parts.-/
noncomputable def partitionCost (g : ℕ) (b : ι → ℕ) (part : ι → Fin g) : ℚ :=
  (∑ t : Fin g, ∏ i ∈ univ with part i = t, (1 - (1 : ℚ) / b i)) / g

/-- The entire set of achievable uncovered densities is exactly the set of
values of the product expression in (11.1).-/
theorem common_gcd_product_optimization (g : ℕ) (hg : 0 < g)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (hc : ∀ i j, i ≠ j → (b i).Coprime (b j)) (u : ℚ) :
    (∃ a : ι → ℤ, 1 - density univ (fun i => g * b i) a = u) ↔
      ∃ part : ι → Fin g, partitionCost g b part = u := by
  have hn : ∀ i, 0 < g * b i := fun i => Nat.mul_pos hg (hb i)
  have hgc : ∀ i j, i ≠ j → (g * b i).gcd (g * b j) = g := by
    intro i j hij
    rw [Nat.gcd_mul_left, (hc i j hij).gcd_eq_one, mul_one]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨part, hp⟩ := (common_gcd_partition_optimization
      (fun i => g * b i) hn g hg hgc (density univ (fun i => g * b i) a)).mp ⟨a, rfl⟩
    refine ⟨part, ?_⟩
    change (∑ t : Fin g, ∏ i ∈ univ with part i = t, (1 - (1 : ℚ) / b i)) / g = u
    rw [← common_gcd_uncovered_formula univ g hg b (fun i _ => hb i) hc part, hp]
    exact ha
  · rintro ⟨part, hp⟩
    exact ⟨fun i => (part i : ℤ),
      (common_gcd_uncovered_formula univ g hg b (fun i _ => hb i) hc part).trans hp⟩

/-- Formula (11.1) with both optima attained: a maximum-density residue choice
and a minimizing partition have exactly complementary objective values.-/
theorem common_gcd_optimum_product_formula (g : ℕ) (hg : 0 < g)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (hc : ∀ i j, i ≠ j → (b i).Coprime (b j)) :
    ∃ (a : ι → ℤ) (part : ι → Fin g),
      (∀ x, density univ (fun i => g * b i) x ≤ density univ (fun i => g * b i) a) ∧
      1 - density univ (fun i => g * b i) a = partitionCost g b part ∧
      (∀ other, partitionCost g b part ≤ partitionCost g b other) := by
  obtain ⟨a, ha⟩ := maximum_attained (fun i => g * b i) (fun i => Nat.mul_pos hg (hb i))
  obtain ⟨part, hp⟩ := (common_gcd_product_optimization g hg b hb hc
    (1 - density univ (fun i => g * b i) a)).mp ⟨a, rfl⟩
  refine ⟨a, part, ha, hp.symm, fun other => ?_⟩
  obtain ⟨x, hx⟩ := (common_gcd_product_optimization g hg b hb hc
    (partitionCost g b other)).mpr ⟨other, rfl⟩
  rw [hp, ← hx]
  linarith [ha x]

end Erdos278
