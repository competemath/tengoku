import Tengoku.Twinprime.TwinPrime.Analytic.DyadicMaximal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite dyadic covers of integer intervals

A block is coded by its starting point and its height, with length `2^height`.
The recursive cover selects a whole root when possible, otherwise descends
into one child or combines a suffix of the left child and a prefix of the right.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- All block codes in a complete binary interval tree.-/
def dyadicTreeBlocks (M : ℕ) : ℕ → Finset (ℕ × ℕ)
  | 0 => {(M, 0)}
  | k + 1 => insert (M, k + 1)
      (dyadicTreeBlocks M k ∪ dyadicTreeBlocks (M + 2 ^ k) k)

theorem mem_dyadicTreeBlocks_bounds (M k : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ dyadicTreeBlocks M k) :
    M ≤ p.1 ∧ p.1 + 2 ^ p.2 ≤ M + 2 ^ k ∧ p.2 ≤ k := by
  induction k generalizing M with
  | zero =>
      have heq : p = (M, 0) := by simpa [dyadicTreeBlocks] using hp
      subst p
      simp
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have hpos : 0 < 2 ^ k := by positivity
      rcases mem_insert.mp hp with heq | hp
      · subst p
        simp
      · rcases mem_union.mp hp with hl | hr
        · obtain ⟨h1, h2, h3⟩ := ih M hl
          exact ⟨h1, h2.trans (by omega), h3.trans (Nat.le_succ _)⟩
        · obtain ⟨h1, h2, h3⟩ := ih (M + 2 ^ k) hr
          exact ⟨le_trans (by omega) h1, h2.trans (by omega), h3.trans (Nat.le_succ _)⟩

theorem dyadicTreeBlocks_children_disjoint (M k : ℕ) :
    Disjoint (dyadicTreeBlocks M k) (dyadicTreeBlocks (M + 2 ^ k) k) := by
  apply disjoint_left.mpr
  intro p hl hr
  have hlb := mem_dyadicTreeBlocks_bounds M k p hl
  have hrb := mem_dyadicTreeBlocks_bounds (M + 2 ^ k) k p hr
  have hpos : 0 < 2 ^ p.2 := by positivity
  omega

theorem dyadicTreeBlocks_root_not_mem_children (M k : ℕ) :
    (M, k + 1) ∉ dyadicTreeBlocks M k ∪ dyadicTreeBlocks (M + 2 ^ k) k := by
  intro hp
  rcases mem_union.mp hp with hl | hr
  · have h := (mem_dyadicTreeBlocks_bounds M k (M, k + 1) hl).2.2
    omega
  · have h := (mem_dyadicTreeBlocks_bounds (M + 2 ^ k) k (M, k + 1) hr).2.2
    omega

/-- Dyadic blocks selected to cover `[u,v)` within the root `[M,M+2^k)`.-/
def dyadicIntervalCover (M : ℕ) : ℕ → ℕ → ℕ → Finset (ℕ × ℕ)
  | 0, u, v => if u < v then {(M, 0)} else ∅
  | k + 1, u, v =>
    if u < v then
      if u = M ∧ v = M + 2 ^ (k + 1) then {(M, k + 1)}
      else if v ≤ M + 2 ^ k then dyadicIntervalCover M k u v
      else if M + 2 ^ k ≤ u then dyadicIntervalCover (M + 2 ^ k) k u v
      else dyadicIntervalCover M k u (M + 2 ^ k) ∪
        dyadicIntervalCover (M + 2 ^ k) k (M + 2 ^ k) v
    else ∅

theorem dyadicIntervalCover_eq_empty (M k u v : ℕ) (hvu : v ≤ u) :
    dyadicIntervalCover M k u v = ∅ := by
  cases k <;> simp [dyadicIntervalCover, not_lt.mpr hvu]

theorem dyadicIntervalCover_full (M k : ℕ) :
    dyadicIntervalCover M k M (M + 2 ^ k) = {(M, k)} := by
  have hp : 0 < 2 ^ k := by positivity
  cases k <;> simp [dyadicIntervalCover, hp]

/-- Every selected code is a genuine node of the enclosing dyadic tree.-/
theorem dyadicIntervalCover_subset_tree (M k u v : ℕ) :
    dyadicIntervalCover M k u v ⊆ dyadicTreeBlocks M k := by
  induction k generalizing M u v with
  | zero => simp only [dyadicIntervalCover]; split_ifs <;> simp [dyadicTreeBlocks]
  | succ k ih =>
      rw [dyadicIntervalCover, dyadicTreeBlocks]
      split_ifs
      · exact singleton_subset_iff.mpr (mem_insert_self _ _)
      · exact (ih M u v).trans (subset_union_left.trans (subset_insert _ _))
      · exact (ih (M + 2 ^ k) u v).trans (subset_union_right.trans (subset_insert _ _))
      · exact (union_subset_union (ih M u (M + 2 ^ k))
          (ih (M + 2 ^ k) (M + 2 ^ k) v)).trans (subset_insert _ _)
      · exact empty_subset _

/-- Every selected block is nonempty and contained in the target interval;
its height does not exceed that of the root.-/
theorem mem_dyadicIntervalCover_bounds (M k u v : ℕ)
    (hMu : M ≤ u) (huv : u ≤ v) (hv : v ≤ M + 2 ^ k)
    (p : ℕ × ℕ) (hp : p ∈ dyadicIntervalCover M k u v) :
    u ≤ p.1 ∧ p.1 + 2 ^ p.2 ≤ v ∧ p.2 ≤ k := by
  induction k generalizing M u v with
  | zero =>
      have huvl : u < v := by
        by_contra h
        simp [dyadicIntervalCover, h] at hp
      have hpm : p = (M, 0) := by simpa [dyadicIntervalCover, huvl] using hp
      subst p
      simp only [pow_zero] at hv
      simp only [pow_zero]
      omega
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have huvl : u < v := by
        by_contra h
        simp [dyadicIntervalCover, h] at hp
      simp only [dyadicIntervalCover, ite_eq_left huvl] at hp
      split_ifs at hp with hfull hleft hright
      · have hpm : p = (M, k + 1) := mem_singleton.mp hp
        subst p
        exact ⟨hfull.1.le, hfull.2.ge, le_rfl⟩
      · obtain ⟨h1, h2, h3⟩ := ih M u v hMu huv hleft hp
        exact ⟨h1, h2, h3.trans (Nat.le_succ _)⟩
      · obtain ⟨h1, h2, h3⟩ := ih (M + 2 ^ k) u v hright huv (by omega) hp
        exact ⟨h1, h2, h3.trans (Nat.le_succ _)⟩
      · rcases mem_union.mp hp with hp | hp
        · obtain ⟨h1, h2, h3⟩ := ih M u (M + 2 ^ k) hMu (by omega) le_rfl hp
          exact ⟨h1, h2.trans (by omega), h3.trans (Nat.le_succ _)⟩
        · obtain ⟨h1, h2, h3⟩ := ih (M + 2 ^ k) (M + 2 ^ k) v le_rfl
            (by omega) (by omega) hp
          exact ⟨le_trans (by omega) h1, h2, h3.trans (Nat.le_succ _)⟩

/-- Covers of disjoint target intervals cannot select the same block.-/
theorem dyadicIntervalCover_disjoint_of_intervals (M k u v M' k' u' v' : ℕ)
    (hMu : M ≤ u) (huv : u ≤ v) (hv : v ≤ M + 2 ^ k)
    (hMu' : M' ≤ u') (huv' : u' ≤ v') (hv' : v' ≤ M' + 2 ^ k')
    (hdis : Disjoint (Ico u v) (Ico u' v')) :
    Disjoint (dyadicIntervalCover M k u v) (dyadicIntervalCover M' k' u' v') := by
  apply disjoint_left.mpr
  intro p hp hp'
  obtain ⟨h1, h2, _⟩ := mem_dyadicIntervalCover_bounds M k u v hMu huv hv p hp
  obtain ⟨h1', h2', _⟩ := mem_dyadicIntervalCover_bounds M' k' u' v' hMu' huv' hv' p hp'
  have hpos : 0 < 2 ^ p.2 := by positivity
  exact disjoint_left.mp hdis (mem_Ico.mpr ⟨h1, by omega⟩)
    (mem_Ico.mpr ⟨h1', by omega⟩)

/-- A prefix selects at most one block for each possible height.-/
theorem card_dyadicIntervalCover_prefix_le (M k v : ℕ)
    (hMv : M ≤ v) (hv : v ≤ M + 2 ^ k) :
    (dyadicIntervalCover M k M v).card ≤ k + 1 := by
  induction k generalizing M v with
  | zero => simp only [dyadicIntervalCover]; split_ifs <;> simp
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have hpos : 0 < 2 ^ k := by positivity
      rw [dyadicIntervalCover]
      split_ifs with hne hfull hleft hright
      · simp
      · exact (ih M v hMv hleft).trans (by omega)
      · omega
      · apply (card_union_le _ _).trans
        rw [dyadicIntervalCover_full, card_singleton]
        have h := ih (M + 2 ^ k) v (by omega) (by omega)
        omega
      · simp

/-- A suffix also selects at most one block for each possible height.-/
theorem card_dyadicIntervalCover_suffix_le (M k u : ℕ)
    (hMu : M ≤ u) (hu : u ≤ M + 2 ^ k) :
    (dyadicIntervalCover M k u (M + 2 ^ k)).card ≤ k + 1 := by
  induction k generalizing M u with
  | zero => simp only [dyadicIntervalCover]; split_ifs <;> simp
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have hpos : 0 < 2 ^ k := by positivity
      rw [dyadicIntervalCover]
      split_ifs with hne hfull hleft hright
      · simp
      · omega
      · have h := ih (M + 2 ^ k) u hright (by omega)
        have heq : M + 2 ^ (k + 1) = (M + 2 ^ k) + 2 ^ k := by omega
        rw [heq]
        exact h.trans (by omega)
      · apply (card_union_le _ _).trans
        have heq : M + 2 ^ (k + 1) = (M + 2 ^ k) + 2 ^ k := by omega
        rw [heq, dyadicIntervalCover_full, card_singleton]
        have h := ih M u hMu (by omega)
        omega
      · simp

/-- An arbitrary subinterval uses at most twice the number of tree levels.-/
theorem card_dyadicIntervalCover_le (M k u v : ℕ)
    (hMu : M ≤ u) (huv : u ≤ v) (hv : v ≤ M + 2 ^ k) :
    (dyadicIntervalCover M k u v).card ≤ 2 * (k + 1) := by
  induction k generalizing M u v with
  | zero => simp only [dyadicIntervalCover]; split_ifs <;> simp
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      rw [dyadicIntervalCover]
      split_ifs with hne hfull hleft hright
      · simp; omega
      · exact (ih M u v hMu huv hleft).trans (by omega)
      · exact (ih (M + 2 ^ k) u v hright huv (by omega)).trans (by omega)
      · apply (card_union_le _ _).trans
        have hl := card_dyadicIntervalCover_suffix_le M k u hMu (by omega)
        have hr := card_dyadicIntervalCover_prefix_le (M + 2 ^ k) k v (by omega) (by omega)
        omega
      · simp

/-- Exact finite sum decomposition for the selected dyadic blocks.-/
theorem sum_dyadicIntervalCover {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    (M k u v : ℕ) (hMu : M ≤ u) (huv : u ≤ v) (hv : v ≤ M + 2 ^ k) :
    (∑ p ∈ dyadicIntervalCover M k u v, ∑ n ∈ Ico p.1 (p.1 + 2 ^ p.2), f n) =
      ∑ n ∈ Ico u v, f n := by
  induction k generalizing M u v with
  | zero =>
      by_cases hlt : u < v
      · have hu : u = M := by norm_num at hv; omega
        have hv' : v = M + 1 := by norm_num at hv; omega
        subst u
        subst v
        simp [dyadicIntervalCover]
      · rw [dyadicIntervalCover_eq_empty M 0 u v (by omega),
          Ico_eq_empty_of_le (by omega)]
        simp
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      rw [dyadicIntervalCover]
      split_ifs with hne hfull hleft hright
      · rcases hfull with ⟨rfl, rfl⟩
        simp
      · exact ih M u v hMu huv hleft
      · exact ih (M + 2 ^ k) u v hright huv (by omega)
      · have hd := dyadicIntervalCover_disjoint_of_intervals M k u (M + 2 ^ k)
          (M + 2 ^ k) k (M + 2 ^ k) v hMu (by omega) le_rfl le_rfl
          (by omega) (by omega) (Ico_disjoint_Ico_consecutive _ _ _)
        rw [sum_union hd, ih M u (M + 2 ^ k) hMu (by omega) le_rfl,
          ih (M + 2 ^ k) (M + 2 ^ k) v le_rfl (by omega) (by omega)]
        exact sum_Ico_consecutive f (by omega) (by omega)
      · rw [Ico_eq_empty_of_le (by omega)]
        simp

/-- Squared triangle inequality followed by finite Cauchy--Schwarz.-/
theorem norm_sum_sq_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖z i‖)

/-- One interval is bounded using only its selected tree nodes.-/
theorem norm_interval_sq_le_dyadicCover (f : ℕ → ℂ) (M k u v : ℕ)
    (hMu : M ≤ u) (huv : u ≤ v) (hv : v ≤ M + 2 ^ k) :
    ‖∑ n ∈ Ico u v, f n‖ ^ 2 ≤
      (2 * ((k : ℝ) + 1)) *
        ∑ p ∈ dyadicIntervalCover M k u v, ‖∑ n ∈ Ico p.1 (p.1 + 2 ^ p.2), f n‖ ^ 2 := by
  rw [← sum_dyadicIntervalCover f M k u v hMu huv hv]
  apply (norm_sum_sq_le_card_mul_sum_sq _ _).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact_mod_cast card_dyadicIntervalCover_le M k u v hMu huv hv

/-- The square sums over any disjoint family of subintervals are controlled
by the complete dyadic tree, without any factor for the number of intervals.-/
theorem sum_disjoint_intervals_sq_le_tree {ι : Type*} (s : Finset ι)
    (u v : ι → ℕ) (f : ℕ → ℂ) (M k : ℕ)
    (hvalid : ∀ i ∈ s, M ≤ u i ∧ u i ≤ v i ∧ v i ≤ M + 2 ^ k)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ico (u i) (v i)) (Ico (u j) (v j))) :
    (∑ i ∈ s, ‖∑ n ∈ Ico (u i) (v i), f n‖ ^ 2) ≤
      (2 * ((k : ℝ) + 1)) *
        ∑ p ∈ dyadicTreeBlocks M k, ‖∑ n ∈ Ico p.1 (p.1 + 2 ^ p.2), f n‖ ^ 2 := by
  let c : ι → Finset (ℕ × ℕ) := fun i => dyadicIntervalCover M k (u i) (v i)
  have hc : Set.PairwiseDisjoint (↑s) c := by
    intro i hi j hj hij
    obtain ⟨hi1, hi2, hi3⟩ := hvalid i hi
    obtain ⟨hj1, hj2, hj3⟩ := hvalid j hj
    exact dyadicIntervalCover_disjoint_of_intervals M k (u i) (v i) M k (u j) (v j)
      hi1 hi2 hi3 hj1 hj2 hj3 (hdis i hi j hj hij)
  have hsub : s.biUnion c ⊆ dyadicTreeBlocks M k := by
    intro p hp
    obtain ⟨i, _, hip⟩ := mem_biUnion.mp hp
    exact dyadicIntervalCover_subset_tree M k (u i) (v i) hip
  calc
    _ ≤ ∑ i ∈ s, (2 * ((k : ℝ) + 1)) *
        ∑ p ∈ c i, ‖∑ n ∈ Ico p.1 (p.1 + 2 ^ p.2), f n‖ ^ 2 := by
      apply sum_le_sum
      intro i hi
      obtain ⟨hi1, hi2, hi3⟩ := hvalid i hi
      exact norm_interval_sq_le_dyadicCover f M k (u i) (v i) hi1 hi2 hi3
    _ = (2 * ((k : ℝ) + 1)) *
        ∑ p ∈ s.biUnion c, ‖∑ n ∈ Ico p.1 (p.1 + 2 ^ p.2), f n‖ ^ 2 := by
      rw [sum_biUnion hc, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)) (by positivity)

/-- The explicit node sum is exactly the recursively defined tree energy.-/
theorem sum_dyadicTreeBlocks_eq_energy (f : ℕ → ℂ) (M k : ℕ) :
    (∑ p ∈ dyadicTreeBlocks M k, ‖∑ n ∈ Ico p.1 (p.1 + 2 ^ p.2), f n‖ ^ 2) =
      dyadicEnergy f M k := by
  induction k generalizing M with
  | zero => simp [dyadicTreeBlocks, dyadicEnergy]
  | succ k ih =>
      rw [dyadicTreeBlocks, sum_insert (dyadicTreeBlocks_root_not_mem_children M k),
        sum_union (dyadicTreeBlocks_children_disjoint M k), ih M, ih (M + 2 ^ k)]
      simp only [dyadicEnergy]
      ring

/-- The finite disjoint-interval variation bound, with loss `2(k+1)`.-/
theorem sum_disjoint_intervals_sq_le_dyadicEnergy {ι : Type*} (s : Finset ι)
    (u v : ι → ℕ) (f : ℕ → ℂ) (M k : ℕ)
    (hvalid : ∀ i ∈ s, M ≤ u i ∧ u i ≤ v i ∧ v i ≤ M + 2 ^ k)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ico (u i) (v i)) (Ico (u j) (v j))) :
    (∑ i ∈ s, ‖∑ n ∈ Ico (u i) (v i), f n‖ ^ 2) ≤
      (2 * ((k : ℝ) + 1)) * dyadicEnergy f M k := by
  simpa only [sum_dyadicTreeBlocks_eq_energy] using
    sum_disjoint_intervals_sq_le_tree s u v f M k hvalid hdis

/-- Fixed-interval second moments control disjoint interval families that
may depend on the outer index. The cost is `2(k+1)^2`, independently of the
number of intervals in each family.-/
theorem sum_weighted_disjoint_intervals_sq_le {ι κ : Type*} (s : Finset ι)
    (t : ι → Finset κ) (u v : ι → κ → ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (f : ι → ℕ → ℂ) (e : ℕ → ℝ) (A : ℝ)
    (he : ∀ n, 0 ≤ e n)
    (hLS : ∀ a b : ℕ, (∑ i ∈ s, w i * ‖∑ n ∈ Ico a b, f i n‖ ^ 2) ≤
      (((b - a : ℕ) : ℝ) + A) * ∑ n ∈ Ico a b, e n)
    (M k : ℕ)
    (hvalid : ∀ i ∈ s, ∀ j ∈ t i,
      M ≤ u i j ∧ u i j ≤ v i j ∧ v i j ≤ M + 2 ^ k)
    (hdis : ∀ i ∈ s, ∀ j ∈ t i, ∀ j' ∈ t i, j ≠ j' →
      Disjoint (Ico (u i j) (v i j)) (Ico (u i j') (v i j'))) :
    (∑ i ∈ s, w i * ∑ j ∈ t i, ‖∑ n ∈ Ico (u i j) (v i j), f i n‖ ^ 2) ≤
      (2 * ((k : ℝ) + 1) ^ 2) * ((2 : ℝ) ^ k + A) *
        ∑ n ∈ Ico M (M + 2 ^ k), e n := by
  calc
    _ ≤ ∑ i ∈ s, w i * ((2 * ((k : ℝ) + 1)) * dyadicEnergy (f i) M k) := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (sum_disjoint_intervals_sq_le_dyadicEnergy (t i) (u i) (v i) (f i) M k
          (hvalid i hi) (hdis i hi)) (hw i hi)
    _ = (2 * ((k : ℝ) + 1)) * ∑ i ∈ s, w i * dyadicEnergy (f i) M k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ (2 * ((k : ℝ) + 1)) * (((k : ℝ) + 1) * ((2 : ℝ) ^ k + A) *
        ∑ n ∈ Ico M (M + 2 ^ k), e n) :=
      mul_le_mul_of_nonneg_left (sum_weighted_dyadicEnergy_le s w f e A he hLS M k)
        (by positivity)
    _ = _ := by ring

end TwinPrime.Analytic
