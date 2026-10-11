/-
Copyright (c) 2026 Tom Adamczewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Adamczewski
-/

module

public import Tengoku.LeanPool.LeanPool.Erdos548.RootedTrees
public import Tengoku

/-!
# Erdős problem 548: the Erdős–Sós conjecture

*Reference:* [erdosproblems.com/548](https://www.erdosproblems.com/548)

Every graph on `n ≥ k + 1` vertices with at least `(k - 1) n / 2 + 1` edges contains every tree on
`k + 1` vertices (`erdos_548`).

## Proof outline

For each permutation word of the host vertices, distinguish its first vertex as a root image.
Count the prefixes of its remaining word which end at a neighbour of that root image and support
a rooted copy of the target tree.

Two reversible word operations provide the induction:
* Rotating the first qualifying prefix past the rest of a prefix gives the branch-gluing
  inequality (`marked_word_gluing_count`).
* Reversing both blocks at a cut moves the root to a newly attached leaf, losing at most one
  state per full word (`rooted_word_leaf_move_count`).

Splitting at a nonleaf root, or deleting a leaf root, then proves `rooted_word_tree_bound`: the
number of all adjacency-marked states is at most the rooted-copy count plus `(t - 2) * n!` for a
target of order `t ≥ 2`. The marked-state count is exactly `2 * |E(G)| * (n - 1)!`
(`full_word_base_count`). If the target is absent, cancellation yields `2 * |E(G)| ≤ (t - 2) * n`
(`tree_free_edge_bound`), contradicting the stated density. All counts and injections are finite
and exact.
-/

@[expose] public section

open SimpleGraph

namespace Erdos548

lemma full_word_base_count {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (l₀ : List V) (hl : l₀.Nodup) (hall : ∀ b, b ∈ l₀) :
    fullWordCount l₀ G.Adj (fun _ _ => True) =
      (l₀.length - 1).factorial * (2 * G.edgeSet.ncard) := by
  classical
  cases nonempty_fintype V
  have hset : l₀.toFinset = Finset.univ := by
    ext b
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hall b
  have hfiber : ∀ b ∈ l₀.toFinset,
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length - 1) (G.Adj b)
        (fun _ => True)).card = (l₀.length - 1).factorial * G.degree b := by
    intro b hb
    have hlen : ∀ q ∈ permutationWords (l₀.erase b), q.length = l₀.length - 1 := by
      intro q hq
      rw [((mem_permutationWords _ _).mp hq).length_eq, List.length_erase_of_mem (hall b)]
    have hnodup : ∀ q ∈ permutationWords (l₀.erase b), q.Nodup := by
      intro q hq
      exact ((mem_permutationWords _ _).mp hq).nodup_iff.mpr (hl.erase b)
    rw [goodWordCuts_true_card _ _ _ hlen hnodup]
    have hterm : ∀ q ∈ permutationWords (l₀.erase b),
        (q.toFinset.filter (G.Adj b)).card = G.degree b := by
      intro q hq
      have hp : (b::q).Perm l₀ := List.cons_perm_iff_perm_erase.mpr
        ⟨hall b, (mem_permutationWords _ _).mp hq⟩
      have he : q.toFinset.filter (G.Adj b) = G.neighborFinset b := by
        ext v
        simp only [Finset.mem_filter, List.mem_toFinset, G.mem_neighborFinset]
        constructor
        · exact And.right
        · intro hv
          constructor
          · have hm : v ∈ b::q := hp.mem_iff.mpr (hall v)
            exact (List.mem_cons.mp hm).resolve_left (fun hh => hv.ne hh.symm)
          · exact hv
      rw [he, G.card_neighborFinset_eq_degree]
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_const, nsmul_eq_mul, permutationWords_card _ (hl.erase b),
      List.length_erase_of_mem (hall b), Nat.cast_id]
  rw [fullWordCount_eq_sum, Finset.sum_congr rfl hfiber, ← Finset.mul_sum, hset,
    G.sum_degrees_eq_twice_card_edges]
  congr 2
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card]
  rfl

end Erdos548
