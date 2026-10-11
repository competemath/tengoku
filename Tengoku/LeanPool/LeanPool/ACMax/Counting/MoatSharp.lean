/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku.LeanPool.LeanPool.ACMax.Counting.CompactCell
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.Moats

/-!
# The bulk-credited master-cycle moat (`master_cycle_fires_sharp`)

`master_cycle_fires` (`Counting/Moats.lean`) bounds the outer boundary `∂₂ ≤ Σ_F(deg − 1)` and
then caps `Σ_F(deg − 3)` by the *whole* excess budget `n − 8`, via `F ∪ S₁ ⊆ univ`.  That step
throws away `Σ_{S₂}(deg − 3)`, the excess sitting in the **bulk** — which, on the starved census,
is the bulk of the excess: only `n₃ = X + 8` vertices have degree `3`, so every one of the other
`|S₂| − n₃` bulk vertices spends at least `1`.

Keeping that term turns the ledger into an identity over the partition `S₁ ⊔ F ⊔ S₂ = univ` and
replaces the firing threshold

  `3·Σ_{S₁}(deg − 1) ≤ n + 8`     (i.e. `9k ≤ n + 8` on a degree-`≤ 4` cycle)

by the strictly weaker

  `4·Σ_{S₁} deg + n₃ ≤ 2n + 8 + 4k`   (i.e. `12k + n₃ ≤ 2n + 8`, i.e. `12k + X ≤ 2n`).

Since the hoarding law gives `3X + 26 ≤ n`, the new threshold dominates the old at *every* cell:
the forbidden cycle length rises from `(n+8)/9` to `(2n − X)/12`, a factor `1.2`–`1.5`.

Everything else — the slice bound, the moat cap `|F| ≤ Σ_{S₁}(deg − 2)`, the two-cluster tie — is
verbatim `master_cycle_fires`; only the ledger and the threshold change.
-/

@[expose] public section

namespace ACMax

open Finset

open Classical in
/-- **The degree-`3` census identity** `n₃ = X + 8`.  From the excess ledger
`Σ_v (deg v − 3) = n − 8`: a degree-`3` vertex spends `0`, and every other vertex spends
`(deg − 4) + 1`, so `n − 8 = X + (n − n₃)`. -/
theorem n3_eq_excess_add_eight {n : ℕ} (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card = excessX n G + 8 := by
  classical
  have htot := total_excess_eq hn G hm h3
  set A := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hA
  set B := Finset.univ.filter (fun v : Fin n => ¬ G.degree v = 3) with hB
  have hcard : A.card + B.card = n := by
    rw [hA, hB, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hsplit : (∑ v ∈ A, (G.degree v - 3)) + (∑ v ∈ B, (G.degree v - 3)) = n - 8 := by
    rw [hA, hB, Finset.sum_filter_add_sum_filter_not]; exact htot
  have hA0 : (∑ v ∈ A, (G.degree v - 3)) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [hA, Finset.mem_filter] at hv
    omega
  have hBval : (∑ v ∈ B, (G.degree v - 3)) = (∑ v ∈ B, (G.degree v - 4)) + B.card := by
    have hpt : ∀ v ∈ B, G.degree v - 3 = (G.degree v - 4) + 1 := by
      intro v hv
      rw [hB, Finset.mem_filter] at hv
      have := h3 v
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hexc : (∑ v ∈ B, (G.degree v - 4)) = excessX n G := by
    unfold excessX
    refine (Finset.sum_subset ?_ ?_).symm
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro v hv hv2
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2
      have := h3 v
      omega
  omega

end ACMax
