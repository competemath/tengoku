/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.Ind2K2

/-!
# The quotient (class-vector) master certificate

The opening move of the quotient program for the mid-range
`19 ≤ n ≤ 598 693`: by Haemers interlacing, for *any* partition of the vertex
set into `m` classes, `λ₂(G)` is at most the second eigenvalue of the `m×m`
quotient matrix — and for the *second* eigenvalue specifically, the quotient
bound is witnessed by a **class-constant test vector**, so it follows from the
universal single-vector certificate.  The value of the packaging is that the
Rayleigh data reduces to *aggregate* quantities: class sizes and inter-class
edge counts, exactly what the campaign's counting machinery produces.

* `classSize c i` — the size of class `i`;
* `interEdges G c i j` — the number of **ordered** adjacent pairs `(u,v)` with
  `u` in class `i` and `v` in class `j` (`interEdges i j = interEdges j i`;
  the diagonal counts internal edges twice but is killed by `(x i − x i)² = 0`);
* `algConn_le_two_of_class_vector` — the master: a class-valued vector `x`
  with `Σᵢ nᵢ xᵢ = 0` and

    `Σᵢⱼ Eᵢⱼ (xᵢ − xⱼ)² ≤ 4·Σᵢ nᵢ xᵢ²`

  certifies `algConn G ≤ 2`  (the `4` is `2 × 2`: one factor because ordered
  pairs double-count edges, one from the target `λ₂ ≤ 2`);
* `algConn_le_two_of_sparse_cut` — the classical Fiedler cut bound as the
  `m = 2` instance: `n·e(S, Sᶜ) ≤ 2·|S|·|Sᶜ|` certifies `algConn ≤ 2`
  (stated with the ordered cross count: `n·E ≤ 4·|S|·|Sᶜ|`);
* degree-class handshake identities on the residual cell, expressing the
  quotient data of the degree partition `{3}/{4}/{≥5}` in ledger terms.
-/

@[expose] public section

namespace ACMax

open Finset

variable {V : Type*} [Fintype V]

/-! ## Quotient data -/

open Classical in
/-- The size of class `i` under the class map `c`. -/
noncomputable def classSize {m : ℕ} (c : V → Fin m) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun v => c v = i)).card

open Classical in
/-- The number of **ordered** adjacent pairs from class `i` to class `j`. -/
noncomputable def interEdges {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) : ℕ :=
  ((Finset.univ.filter (fun v => c v = i)) ×ˢ
    (Finset.univ.filter (fun v => c v = j))).filter
      (fun p => G.Adj p.1 p.2) |>.card

open Classical in
/-- Fiberwise decomposition of a vertex sum by classes.
@isnad1 id=eq.0h5v.s6.76f4fa5d1993 from=translated src=- shape=94e861ca vocab=8a998268
-/
theorem sum_classes {m : ℕ} {M : Type*} [AddCommMonoid M]
    (c : V → Fin m) (f : V → M) :
    ∑ v : V, f v
      = ∑ i : Fin m, ∑ v ∈ Finset.univ.filter (fun v => c v = i), f v :=
  (Finset.sum_fiberwise Finset.univ c f).symm

open Classical in
/-- A class-constant square sum aggregates to class sizes.
@isnad1 id=eq.0h4v.s6.b69dd503b115 from=translated src=- shape=d6a34da5 vocab=523502ab
-/
theorem sum_sq_classes {m : ℕ} (c : V → Fin m) (x : Fin m → ℝ) :
    ∑ v : V, x (c v) ^ 2
      = ∑ i : Fin m, (classSize c i : ℝ) * x i ^ 2 := by
  rw [sum_classes c (fun v => x (c v) ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (fun v hv => by
    rw [(Finset.mem_filter.mp hv).2]), Finset.sum_const, nsmul_eq_mul]
  rfl

open Classical in
/-- The inter-class count as a double indicator sum over the fibers.
@isnad1 id=eq.0h6v.s6.8ec2e8e05831 from=translated src=- shape=8f987dcb vocab=8711aa61
-/
theorem interEdges_eq_sum {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) :
    (interEdges G c i j : ℝ)
      = ∑ u ∈ Finset.univ.filter (fun v => c v = i),
          ∑ v ∈ Finset.univ.filter (fun v => c v = j),
          (if G.Adj u v then (1 : ℝ) else 0) := by
  classical
  rw [interEdges, Finset.card_filter]
  push_cast
  rw [Finset.sum_product]

open Classical in
/-- The edge quadratic form aggregates to inter-class counts.
@isnad1 id=eq.0h5v.s7.713339873a9b from=translated src=- shape=50b10aa1 vocab=32683980
-/
theorem sum_edge_sq_classes {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (x : Fin m → ℝ) :
    ∑ u : V, ∑ v : V,
        (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
      = ∑ i : Fin m, ∑ j : Fin m,
          (interEdges G c i j : ℝ) * (x i - x j) ^ 2 := by
  classical
  -- fiberwise in `u`, then in `v`
  rw [sum_classes c (fun u => ∑ v : V,
    (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hswap : ∑ u ∈ Finset.univ.filter (fun v => c v = i), ∑ v : V,
      (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
      = ∑ j : Fin m, ∑ u ∈ Finset.univ.filter (fun v => c v = i),
          ∑ v ∈ Finset.univ.filter (fun v => c v = j),
          (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0) := by
    have h1 : ∀ u : V, ∑ v : V,
        (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
        = ∑ j : Fin m, ∑ v ∈ Finset.univ.filter (fun v => c v = j),
            (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0) := fun u =>
      (Finset.sum_fiberwise Finset.univ c
        (fun v => if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)).symm
    rw [Finset.sum_congr rfl fun u _ => h1 u]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [interEdges_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2]
  split <;> ring

/-! ## The master certificate -/

/-! ## The classical sparse-cut instance (`m = 2`) -/

/-! ## Handshake identities for the quotient data -/

open Classical in
/-- Inter-class counts are symmetric.
@isnad1 id=eq.0h6v.s5.d898957534ae from=translated src=- shape=d98ae192 vocab=2135a443
-/
theorem interEdges_symm {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) : interEdges G c i j = interEdges G c j i := by
  classical
  rw [interEdges, interEdges]
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩
  · intro p _ q _ hpq
    exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
  · intro p hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩

/-! ## The two-cluster law (`m = 3`) -/

/-! ## The degree-class partition on the residual cell -/

variable {n : ℕ}

/-! ## The two-hub block cut (the endgame seed) -/

end ACMax
