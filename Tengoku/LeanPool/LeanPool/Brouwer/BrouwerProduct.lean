/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
module

public import Tengoku.LeanPool.LeanPool.Brouwer.Simplex
import Tengoku.LeanPool.LeanPool.Brouwer.Brouwer
public import Tengoku

/-!
# Brouwer's fixed-point theorem on a product of simplices

This file extends Brouwer's fixed-point theorem from a single standard simplex to
a finite product of standard simplices. A continuous retraction collapses the big
simplex onto the product, so a fixed point of a continuous self-map of the product
is obtained from the single-simplex theorem.
-/

@[expose] public section

open Brouwer (standardSimplex)

open Filter

section Brouwer.ProductRetraction
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+)

/-- Total number of coordinates: the sum of `card i` over all `i`. -/
noncomputable def totalCard (card : I → ℕ+)
    : ℕ+ := ⟨(Finset.univ : Finset I).sum (fun i => (card i : ℕ)), by
  apply Finset.sum_pos
  · simp
  · exact Finset.univ_nonempty⟩

omit [DecidableEq I] [LinearOrder I] in
private lemma totalCard_pos_real : 0 < (totalCard card : ℝ) := by
  norm_cast; exact PNat.pos (totalCard card)

omit [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] in
private lemma card_pos_real (i : I) : 0 < (card i : ℝ) := by
  norm_cast; exact PNat.pos (card i)

/-- The big simplex on `totalCard card` coordinates. -/
abbrev BigSimplex := standardSimplex ℝ (Fin (totalCard card))

/-- The product of simplices indexed by `I`. -/
abbrev ProductSimplices := (i : I) → standardSimplex ℝ (Fin (card i))

/-- Cumulative sum of `card` over indices strictly less than `i`. -/
noncomputable def prefixSum (card : I → ℕ+) (i : I) : ℕ :=
  ∑ j ∈ Finset.univ.filter (· < i), (card j : ℕ)

/-- Combine a block/index pair `(i, j)` back into a flat index. -/
noncomputable def indexCombine (p : Σ i, Fin (card i)) : Fin (totalCard card) :=
  ⟨prefixSum card p.1 + (p.2 : ℕ), by
    have h1 : prefixSum card p.1 + (p.2 : ℕ) < prefixSum card p.1 + (card p.1 : ℕ) := by
      simpa only [add_lt_add_iff_left] using p.2.is_lt
    have h2 : prefixSum card p.1 + (card p.1 : ℕ) ≤ (totalCard card : ℕ) := by
      simp only [prefixSum, totalCard]
      have h_subset : Finset.univ.filter (· ≤ p.1) ⊆ Finset.univ := Finset.filter_subset _ _
      have h_eq : (Finset.univ.filter (· ≤ p.1)).sum (fun j => (card j : ℕ)) =
                   (Finset.univ.filter (· < p.1)).sum (fun j => (card j : ℕ)) + (card p.1 : ℕ) := by
        have h_split : Finset.univ.filter (· ≤ p.1) = Finset.univ.filter (· < p.1) ∪ {p.1} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_singleton]
          exact le_iff_lt_or_eq
        have h_disj : Disjoint (Finset.univ.filter (· < p.1)) {p.1} := by simp
        rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
      rw [← h_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => by positivity)
    exact lt_of_lt_of_le h1 h2⟩

/-- Weight (size fraction) of block `i`: `(card i) / (totalCard card)`. -/
noncomputable def blockWeight (i : I) : ℝ := (card i : ℝ) / (totalCard card : ℝ)

/-- Sum of coordinates of `x` over the block `i`. -/
noncomputable def blockSum (i : I) (x : BigSimplex card) : ℝ :=
  ∑ j : Fin (card i), x.1 (indexCombine card ⟨i, j⟩)

/-- The uniform point in each block simplex. -/
noncomputable def uniformProduct : ProductSimplices card :=
  fun i =>
    (⟨fun _ => (1 : ℝ) / (card i : ℝ), by
      simp only [standardSimplex, Set.mem_ofPred_eq]
      constructor
      · intro _; apply div_nonneg <;> positivity
      · simp [Finset.sum_const]
    ⟩ : standardSimplex ℝ (Fin (card i)))

/-- The uniform point in the big simplex. -/
noncomputable def zUniform : BigSimplex card :=
  ⟨fun _ => (1 : ℝ) / (totalCard card : ℝ), by
    simp only [standardSimplex, Set.mem_ofPred_eq]
    constructor
    · intro _
      apply div_nonneg
      · norm_num
      · have : 0 < (totalCard card : ℝ) := by
          norm_cast; exact PNat.pos (totalCard card)
        exact le_of_lt this
    · have hpos : 0 < (totalCard card : ℝ) := by
        norm_cast; exact PNat.pos (totalCard card)
      have hcard : (Fintype.card (Fin (totalCard card)) : ℝ) = (totalCard card : ℝ) := by
        simp
      simp [Finset.sum_const, (ne_of_gt hpos)]
  ⟩

/-- Total positive shortfall of block sums relative to block weights. -/
noncomputable def deficit (x : BigSimplex card) : ℝ :=
  ∑ i, max (0 : ℝ) ((blockWeight card i) - blockSum card i x)

/-- Amount to push `x` toward `zUniform` (always in `[0, 1]`). -/
noncomputable def tPush (x : BigSimplex card) : ℝ :=
  (deficit card x) / (1 + deficit card x)

/-- Convex push of `x` toward `zUniform` by amount `tPush`. -/
noncomputable def pushTowardsZ (x : BigSimplex card) : BigSimplex card :=
  ⟨fun k => (1 - tPush card x) * x.1 k + (tPush card x) * (zUniform card).1 k, by
    simp only [standardSimplex, Set.mem_ofPred_eq]
    constructor
    · intro k;
      have hx_nonneg : 0 ≤ x.1 k := x.2.1 k
      have hz_nonneg : 0 ≤ (zUniform card).1 k := (zUniform card).2.1 k
      have h_def_nonneg : 0 ≤ deficit card x := by
        unfold deficit
        apply Finset.sum_nonneg
        intro i _
        exact le_max_left _ _
      have hden_pos : 0 < (1 : ℝ) + deficit card x :=
        add_pos_of_pos_of_nonneg (by norm_num) h_def_nonneg
      have ht_nonneg : 0 ≤ tPush card x := by
        simpa [tPush] using div_nonneg h_def_nonneg (le_of_lt hden_pos)
      have h_t_le_one : tPush card x ≤ 1 := by
        have hle : deficit card x ≤ 1 + deficit card x := by linarith
        have hinv_nonneg : 0 ≤ (1 + deficit card x)⁻¹ :=
          inv_nonneg.mpr (le_of_lt hden_pos)
        have hmul := mul_le_mul_of_nonneg_right hle hinv_nonneg
        have hdiv :
            (deficit card x) / (1 + deficit card x) ≤
              (1 + deficit card x) / (1 + deficit card x) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
        simpa [tPush, div_self (ne_of_gt hden_pos)] using hdiv
      have hone_minus_nonneg : 0 ≤ 1 - tPush card x := by linarith
      have hterm1 : 0 ≤ (1 - tPush card x) * x.1 k := mul_nonneg hone_minus_nonneg hx_nonneg
      have hterm2 : 0 ≤ (tPush card x) * (zUniform card).1 k := mul_nonneg ht_nonneg hz_nonneg
      exact add_nonneg hterm1 hterm2
    · classical
      have hpos_tc : 0 < (totalCard card : ℝ) := by
        norm_cast; exact PNat.pos (totalCard card)
      have hx_sum_all : (∑ k, x.1 k) = 1 := x.2.2
      have hz_sum_all : (∑ k, (zUniform card).1 k) = 1 := by
        simp [zUniform, Finset.sum_const, (ne_of_gt hpos_tc)]
      have hx_sum : (∑ k ∈ Finset.univ, x.1 k) = 1 := by simpa using hx_sum_all
      have hz_sum : (∑ k ∈ Finset.univ, (zUniform card).1 k) = 1 := by simpa using hz_sum_all
      calc
        (∑ k ∈ Finset.univ, ((1 - tPush card x) * x.1 k + (tPush card x) * (zUniform card).1 k))
            = (1 - tPush card x) * (∑ k ∈ Finset.univ, x.1 k) + (tPush card x)
                * (∑ k ∈ Finset.univ, (zUniform card).1 k) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum]
        _ = 1 := by
              simp [hx_sum, hz_sum]
  ⟩

omit [DecidableEq I] [LinearOrder I] in
lemma blockWeight_pos (i : I) : 0 < blockWeight card i :=
  div_pos (card_pos_real card i) (totalCard_pos_real card)

/-- `blockSum card i x` is always nonnegative. -/
lemma blockSum_nonneg (i : I) (x : BigSimplex card) : 0 ≤ blockSum card i x := by
  unfold blockSum
  apply Finset.sum_nonneg
  intro j _
  exact x.2.1 _

/-- `deficit card x` is always nonnegative. -/
lemma deficit_nonneg (x : BigSimplex card) : 0 ≤ deficit card x := by
  unfold deficit
  apply Finset.sum_nonneg
  intro i _
  exact le_max_left _ _

/-- `tPush card x` is always in `[0, 1]`. -/
lemma tPush_mem_Icc (x : BigSimplex card) : tPush card x ∈ Set.Icc (0 : ℝ) 1 := by
  have hdef := deficit_nonneg card x
  have hdenpos : 0 < (1 : ℝ) + deficit card x := by linarith
  refine ⟨?_, ?_⟩
  · simpa [tPush] using div_nonneg hdef (le_of_lt hdenpos)
  · rw [tPush, div_le_one hdenpos]; linarith

/-- The block sum after pushing towards `zUniform` follows a linear formula. -/
lemma blockSum_pushTowardsZ_formula (i : I) (x : BigSimplex card) :
    blockSum card i (pushTowardsZ card x) =
      (1 - tPush card x) * blockSum card i x + (tPush card x) * blockWeight card i := by
  simp [blockSum, pushTowardsZ, sub_eq_add_neg, Finset.sum_add_distrib, Finset.mul_sum,
        zUniform, blockWeight, div_eq_mul_inv, mul_left_comm]

/-- The block sum after pushing towards `zUniform` is always positive. -/
lemma blockSum_pushTowardsZ_pos (i : I) (x : BigSimplex card) :
    0 < blockSum card i (pushTowardsZ card x) := by
  rw [blockSum_pushTowardsZ_formula]
  have h_bw_pos := blockWeight_pos card i
  have h_block_nonneg := blockSum_nonneg card i x
  have ⟨h_t_nonneg, h_t_le_one⟩ := tPush_mem_Icc card x
  have h_one_minus_nonneg : 0 ≤ 1 - tPush card x := by linarith
  by_cases ht0 : tPush card x = 0
  · have h_def0 : deficit card x = 0 := by
      have hden_pos : 0 < 1 + deficit card x :=
        add_pos_of_pos_of_nonneg (by norm_num) (deficit_nonneg card x)
      exact (div_eq_zero_iff.mp ht0).resolve_right (ne_of_gt hden_pos)
    have h_term_le_sum : max 0 (blockWeight card i - blockSum card i x) ≤ deficit card x := by
      classical
      have hnonneg : ∀ i' ∈ (Finset.univ : Finset I),
          0 ≤ max 0 (blockWeight card i' - blockSum card i' x) := fun i' _ => le_max_left _ _
      simpa [deficit] using Finset.single_le_sum hnonneg (by simp)
    have h_bw_le_sum : blockWeight card i ≤ blockSum card i x := by
      have h_term_zero : max 0 (blockWeight card i - blockSum card i x) = 0 :=
        le_antisymm (h_term_le_sum.trans (le_of_eq h_def0)) (le_max_left _ _)
      simpa [sub_nonpos] using (max_eq_left_iff.1 h_term_zero)
    have : 0 < blockSum card i x := lt_of_lt_of_le h_bw_pos h_bw_le_sum
    simpa [ht0] using this
  · have htpos : 0 < tPush card x := lt_of_le_of_ne h_t_nonneg (Ne.symm ht0)
    have : 0 < (tPush card x) * blockWeight card i := mul_pos htpos h_bw_pos
    linarith [mul_nonneg h_one_minus_nonneg h_block_nonneg]

/-- Retraction from the big simplex to the product of simplices. -/
noncomputable def projectToProduct (x : BigSimplex card) : ProductSimplices card :=
  fun i =>
    let y := pushTowardsZ card x
    let s := blockSum card i y
    have hspos : 0 < s := blockSum_pushTowardsZ_pos card i x
    (⟨fun j => y.1 (indexCombine card ⟨i, j⟩) / s, by
      simp only [standardSimplex, Set.mem_ofPred_eq]
      constructor
      · intro j
        have hy := y.2.1 (indexCombine card ⟨i, j⟩)
        exact div_nonneg hy (le_of_lt hspos)
      · classical
        have h :
           (∑ j : Fin (card i), y.1 (indexCombine card ⟨i, j⟩) / s)
             = (∑ j : Fin (card i), y.1 (indexCombine card ⟨i, j⟩)) * s⁻¹ := by
         simp [div_eq_mul_inv, Finset.sum_mul]
        have hsum : (∑ j : Fin (card i), y.1 (indexCombine card ⟨i, j⟩)) = s := rfl
        rw [h, hsum]
        field_simp
    ⟩ : standardSimplex ℝ (Fin (card i)))

/-- Continuity of `blockSum card i`. -/
lemma blockSum_continuous (i : I) : Continuous (blockSum card i) := by
  change Continuous (fun x : BigSimplex card =>
    ∑ j : Fin (card i), x.1 (indexCombine card ⟨i, j⟩))
  apply continuous_finsetSum
  intro j _
  exact (continuous_apply _).comp continuous_subtype_val

/-- Continuity of `deficit card`. -/
lemma deficit_continuous : Continuous (deficit card) := by
  change Continuous (fun x : BigSimplex card =>
    ∑ i, max (0 : ℝ) ((blockWeight card i) - blockSum card i x))
  apply continuous_finsetSum
  intro i _
  exact continuous_const.max (continuous_const.sub (blockSum_continuous card i))

/-- Continuity of `tPush card`. -/
lemma tPush_continuous : Continuous (tPush card) := by
  have h_denom_cont : Continuous (fun x => (1 : ℝ) + deficit card x) :=
    continuous_const.add (deficit_continuous card)
  have h_denom_ne : ∀ x, (1 : ℝ) + deficit card x ≠ 0 := fun x =>
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num) (deficit_nonneg card x))
  exact Continuous.div (deficit_continuous card) h_denom_cont h_denom_ne

/-- Continuity of `pushTowardsZ card`. -/
lemma pushTowardsZ_continuous : Continuous (pushTowardsZ card) := by
  apply Continuous.subtype_mk
  classical
  apply continuous_pi
  intro k
  have hxk : Continuous (fun x : BigSimplex card => x.1 k) :=
    (continuous_apply k).comp continuous_subtype_val
  have hone_minus_t : Continuous (fun x => (1 : ℝ) - tPush card x) :=
    continuous_const.sub (tPush_continuous card)
  have hterm1 : Continuous (fun x => ((1 : ℝ) - tPush card x) * x.1 k) :=
    hone_minus_t.mul hxk
  have hterm2 : Continuous (fun x => (tPush card x) * (zUniform card).1 k) :=
    (tPush_continuous card).mul continuous_const
  have hsum : Continuous
      (fun x : BigSimplex card =>
        ((1 : ℝ) - tPush card x) * x.1 k + (tPush card x) * (zUniform card).1 k) :=
    hterm1.add hterm2
  simpa [pushTowardsZ] using hsum

/-- Continuity of `projectToProduct`. -/
lemma project_continuous : Continuous (projectToProduct card) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  let k : Fin (totalCard card) := indexCombine card ⟨i, j⟩
  have h_num_cont : Continuous (fun x : BigSimplex card => (pushTowardsZ card x).1 k) :=
    (continuous_apply k).comp (continuous_subtype_val.comp (pushTowardsZ_continuous card))
  have h_denom_cont : Continuous (fun x : BigSimplex card =>
      blockSum card i (pushTowardsZ card x)) := by
    change Continuous (fun x : BigSimplex card =>
      ∑ j : Fin (card i), (pushTowardsZ card x).1 (indexCombine card ⟨i, j⟩))
    apply continuous_finsetSum
    intro j _
    exact (continuous_apply (indexCombine card ⟨i, j⟩)).comp
      (continuous_subtype_val.comp (pushTowardsZ_continuous card))
  have h_denom_ne : ∀ x : BigSimplex card, blockSum card i (pushTowardsZ card x) ≠ 0 :=
    fun x => ne_of_gt (blockSum_pushTowardsZ_pos card i x)
  have h_div : Continuous (fun x : BigSimplex card =>
      (pushTowardsZ card x).1 k / blockSum card i (pushTowardsZ card x)) :=
    Continuous.div h_num_cont h_denom_cont h_denom_ne
  simpa [projectToProduct, blockSum] using h_div

end Brouwer.ProductRetraction
