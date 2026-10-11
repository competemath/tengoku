/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku.LeanPool.LeanPool.ACMax.Counting.StarNeighbors
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.Incidence
public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.Moats
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.SparseCore
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.TripleCensus
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.DecoratedC4

/-!
# The sharpened `Z1` star moat

`star_moat_fires` (`Counting/Moats`) fires a degree-`d` hub carrying `d − 2` degree-`3` twins
whenever `9d ≤ n + 15`, which at `d = 4` gives only `n ≥ 21`. That threshold is not
intrinsic: it bounds the outer boundary `∂₂ = e(F, S₂)` from the moat side alone,

  `∂₂ ≤ Σ_F (deg − 1) = E_F + 2|F|`,

and then charging `E_F` against the whole excess budget `n − 8`.  The bulk side is never counted.

This file adds the missing bulk count. Writing `E_F`, `E₂` for the excess carried by the moat `F`
and the bulk
`S₂`, the two sides say

  `∂₂ ≤ E_F + 2f`     (moat side, as before)
  `∂₂ + P₂ = 3|S₂| + E₂` (bulk side: every `S₂`-vertex sends its degree into `F ⊎ S₂`)

with `P₂` the ordered adjacent pairs inside `S₂`. Under `hs0` the degree-`3` vertices of `S₂` are
pairwise non-adjacent, so every `S₂`-edge has an endpoint of degree at least `4` and
`P₂ ≤ 8·E₂`. For `n ≥ 16`, combining this estimate with the moat ledger either fires the
original cut or exposes a sparse bulk core, which supplies another cut certificate. The five
remaining orders `10 ≤ n ≤ 15` have rigid excess profiles; the same ledgers, supplemented by
triangle and decorated-`C₄` certificates at the tight corners, close them directly.
-/

@[expose] public section

namespace ACMax

open Classical in
/-- **The bulk-side pair bound.**  In a starved census (`hs0`: no degree-`3`–degree-`3` edge), the
ordered adjacent pairs inside any set `T` are at most `8·E_T`, where `E_T = Σ_T (deg − 3)`: every
adjacent pair inside `T` has an endpoint of degree `≥ 4`, there are at most `E_T` such vertices in
`T`, and each has degree at most `3 + (deg − 3)`. -/
theorem pairs_le_eight_excess {n : ℕ} (G : SimpleGraph (Fin n))
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (T : Finset (Fin n)) :
    ((T ×ˢ T).filter (fun q => G.Adj q.1 q.2)).card ≤ 8 * ∑ v ∈ T, (G.degree v - 3) := by
  classical
  set A : Finset (Fin n) := T.filter (fun v => 4 ≤ G.degree v) with hA
  set B : Finset (Fin n) := T.filter (fun v => ¬ (4 ≤ G.degree v)) with hB
  set E : ℕ := ∑ v ∈ T, (G.degree v - 3) with hE
  -- the ordered-pair count as a slice sum
  have hcnt : ∀ (X Y : Finset (Fin n)),
      ((X ×ˢ Y).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ X, (G.neighborFinset a ∩ Y).card := by
    intro X Y
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ Y = Y.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- `A ⊎ B = T`
  have hAB : ∑ v ∈ A, (G.neighborFinset v ∩ T).card + ∑ v ∈ B, (G.neighborFinset v ∩ T).card
      = ∑ v ∈ T, (G.neighborFinset v ∩ T).card := by
    rw [hA, hB]
    exact Finset.sum_filter_add_sum_filter_not T _ _
  -- a degree-`3` vertex of `T` has all its `T`-neighbours in `A`
  have hBslice : ∀ v ∈ B, G.neighborFinset v ∩ T = G.neighborFinset v ∩ A := by
    intro v hv
    rw [hB, Finset.mem_filter] at hv
    have hv3 : G.degree v = 3 := by have := h3 v; omega
    ext x
    simp only [Finset.mem_inter, hA, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hxT⟩
      refine ⟨hx, hxT, ?_⟩
      by_contra hlt
      have hx3 : G.degree x = 3 := by have := h3 x; omega
      exact hs0 v x hv3 hx3 ((G.mem_neighborFinset v x).mp hx)
    · rintro ⟨hx, hxT, _⟩; exact ⟨hx, hxT⟩
  -- transpose the `B`-half onto `A`
  have hBA : ∑ v ∈ B, (G.neighborFinset v ∩ T).card ≤ ∑ v ∈ A, (G.neighborFinset v ∩ T).card := by
    calc ∑ v ∈ B, (G.neighborFinset v ∩ T).card
        = ∑ v ∈ B, (G.neighborFinset v ∩ A).card :=
          Finset.sum_congr rfl (fun v hv => by rw [hBslice v hv])
      _ = ∑ w ∈ A, (G.neighborFinset w ∩ B).card := cross_count G B A
      _ ≤ ∑ w ∈ A, (G.neighborFinset w ∩ T).card := by
          refine Finset.sum_le_sum (fun w _ => Finset.card_le_card ?_)
          exact Finset.inter_subset_inter_left (by rw [hB]; exact Finset.filter_subset _ _)
  -- the `A`-half against the excess
  have hAcard : A.card ≤ E := by
    rw [hE, hA]
    calc (T.filter (fun v => 4 ≤ G.degree v)).card
        = ∑ _v ∈ T.filter (fun v => 4 ≤ G.degree v), 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ v ∈ T.filter (fun v => 4 ≤ G.degree v), (G.degree v - 3) := by
          refine Finset.sum_le_sum (fun v hv => ?_)
          have := (Finset.mem_filter.mp hv).2; omega
      _ ≤ ∑ v ∈ T, (G.degree v - 3) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hAexc : ∑ v ∈ A, (G.degree v - 3) ≤ E :=
    Finset.sum_le_sum_of_subset (by rw [hA]; exact Finset.filter_subset _ _)
  have hAdeg : ∑ v ∈ A, (G.neighborFinset v ∩ T).card ≤ 3 * A.card + E := by
    calc ∑ v ∈ A, (G.neighborFinset v ∩ T).card
        ≤ ∑ v ∈ A, G.degree v := by
          refine Finset.sum_le_sum (fun v _ => ?_)
          rw [← G.card_neighborFinset_eq_degree]
          exact Finset.card_le_card Finset.inter_subset_left
      _ = ∑ v ∈ A, ((G.degree v - 3) + 3) :=
          Finset.sum_congr rfl (fun v _ => by have := h3 v; omega)
      _ = (∑ v ∈ A, (G.degree v - 3)) + 3 * A.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ 3 * A.card + E := by omega
  rw [hcnt T T]
  omega

end ACMax
