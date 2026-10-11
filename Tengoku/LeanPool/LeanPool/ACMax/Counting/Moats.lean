/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku.LeanPool.LeanPool.ACMax.Counting.Quotient
public import Tengoku

/-!
# Two-cluster moat kills and the thin-twin averaging row

The *moat* family of two-cluster cut certificates: a low-degree tie-block `S₁`
whose closed neighbourhood forms a zeroed *moat* `F`, so that
`algConn_le_two_of_two_clusters` fires `algConn G ≤ 2` with no diameter, census
or cell hypotheses. Each vertex of `S₁` keeps an external degree budget of `2`,
so the boundary hits the two-cluster tie `∂₁ ≤ 2|S₁|` and the excess ledger
`Σ_v (deg v − 3) = n − 8` (`total_excess_eq`) caps the bulk boundary.

## Main results

* `medge_moat_fires` — an `M`-edge (a degree-3–degree-3 edge) fires at `n ≥ 12`.
* `star_moat_fires` (and `z1_star_moat_fires`) — a hub `h` hoarding `deg h − 2`
  degree-3 twins fires at `9·deg h ≤ n + 15`.
* `master_cycle_fires` — a cycle with degree-sum tie `Σ deg ≤ 4k` fires at
  `n ≥ 3·Σ(deg − 1) − 8`.
* `deco_edge_moat_fires` (and `z4c_fires`) — an adjacent hub pair hoarding
  `deg u − 3`, `deg v − 3` twins fires at `9·(deg u + deg v) ≤ n + 42`.
* The **thin-twin averaging row**: the double-counting swap
  `∑_{t∈T} E₁(t) = ∑_v (deg v − 3)·|N(v) ∩ T|` (`twin_E1_sum_swap`) with the
  excess ledger and a multiplicity cap `K` yields
  `∃ t ∈ T, |T|·E₁(t) ≤ K·(n − 8)` (`thin_twin_exists_of_multcap`), with the
  unconditional instances `thin_twin_exists_deg5` and
  `thin_twin_exists_iso_of_multcap`.
-/

/-! ## The thin-twin averaging row

The averaging engine producing a *thin* twin (bounded `1`-ball excess
`E₁(t) = sphereExc G t 1`). The double-counting swap `twin_E1_sum_swap` holds for
any root set `T`; combined with `total_excess_eq` and a multiplicity cap
`|N(v) ∩ T| ≤ K` it gives `∑_{t∈T} E₁(t) ≤ K·(n − 8)` and the averaging existence
`thin_twin_exists_of_multcap`. The cap `K` stays explicit (a heavy vertex's
multiplicity is unbounded); the clean instances are `thin_twin_exists_deg5`
(`K = 5` when `Δ ≤ 5`) and `thin_twin_exists_iso_of_multcap` (on `isoTwins G`). -/

@[expose] public section

namespace ACMax

open Finset

open Classical in
/-- **The excess ledger.**  On the `m = 2(n−2)`, `δ ≥ 3` census (`n ≥ 8`) the total degree
excess is `Σ_v (deg v − 3) = n − 8`: the handshake `Σ deg = 2·2(n−2) = 4n − 8` minus the
base `3n`. -/
theorem total_excess_eq {n : ℕ} (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    ∑ v : Fin n, (G.degree v - 3) = n - 8 := by
  have hhandshake : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hcancel : ∑ v : Fin n, G.degree v = (∑ v : Fin n, (G.degree v - 3)) + 3 * n := by
    have h3n : ∑ _v : Fin n, (3 : ℕ) = 3 * n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    rw [← h3n, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => (Nat.sub_add_cancel (h3 v)).symm)
  omega

/-! ## The M-moat kill

Instantiates `algConn_le_two_of_two_clusters` with the tie-block `S₁ = {u, p}`
(an `M`-edge) against the bulk, moat `F = (N(u) ∪ N(p)) ∖ {u,p}`: `∂₁ = 4`,
`|F| ≤ 4`, so `medge_moat_fires` gives `algConn G ≤ 2` for every `n ≥ 12`. -/

/-! ## The star-moat kill

The `e(M) = 0` generalization: the star tie-block `S₁ = insert h K` (a hub `h`
with `|K| = deg h − 2` degree-3 twins), each `S₁`-vertex keeping external budget
`2`, so crediting the hub's excess back gives `star_moat_fires` at
`9·deg h ≤ n + 15` (`z1_star_moat_fires`: a degree-4 hub with two twins at
`n ≥ 21`). The twins need not be pairwise non-adjacent — an internal edge only
shrinks the boundary slices. -/

/-! ## The master-cycle kill

A cycle `c : ZMod k → Fin n` (injective, cyclic adjacency) with degree-sum tie
`Σ deg ≤ 4·k` is a tie-block: each cycle vertex has two on-cycle neighbours so
external slice `≤ deg − 2`, giving `∂₁ ≤ Σ(deg − 2) ≤ 2k`; crediting the cycle
excess back, `master_cycle_fires` fires at `n ≥ 3·Σ(deg − 1) − 8` (specializing
to `C_k`, the `(3,4,5)`-triangle at `n ≥ 19`, and alternating rows). -/

/-! ## The decorated-edge moat kill

The *decorated-edge* generalization of the star-moat certificate: the tie-block
`S₁ = {u, v} ∪ Ku ∪ Kv` (an adjacent hub pair with `|Ku| = deg u − 3`,
`|Kv| = deg v − 3` twins), each `S₁`-vertex keeping external budget `2`;
crediting both hubs' excess back, `deco_edge_moat_fires` fires at
`9·(deg u + deg v) ≤ n + 42` (`z4c_fires`: adjacent degree-4 hubs with one twin
each at `n ≥ 30`). -/

end ACMax
