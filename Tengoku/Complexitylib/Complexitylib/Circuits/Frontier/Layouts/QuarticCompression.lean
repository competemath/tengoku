/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Complexitylib.Complexitylib.Circuits.Frontier.Layouts.Compression

/-!
# Compressing graphs of maximum degree four

Merge adjacent blocks whenever their union has at most four outgoing edges. In the final
quotient there are no parallel edges, degrees are three or four, and two degree-three
vertices are never adjacent. Charging weight four to each degree-three endpoint and weight
three to each degree-four endpoint gives `12 |V| ≤ 7 |E|`. The compression invariant then
gives `5 |E(quotient)| ≤ 12 β₁(original)`.
-/

@[expose] public section

namespace Complexity.Frontier.Multigraph.Compression

open Set

variable {V E : Type*} {G : Multigraph V E} {d : ℕ} (c : Compression G d)

/-- No adjacent pair of blocks can still be merged within the degree budget. -/
def Terminal : Prop :=
  ∀ B ∈ c.blocks, ∀ B' ∈ c.blocks, B ≠ B' →
    (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).Nonempty →
      d < (G.cut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard

/-- The block count strictly decreases with every merge, in every degree. -/
theorem exists_terminal [Finite V] [Finite E] (hG : G.MaxDegreeLE d) :
    ∃ c : Compression G d, c.Terminal := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨c, -, hmin⟩ := (measure fun c : Compression G d => c.blocks.card).wf.has_min univ
    ⟨initial hG, trivial⟩
  refine ⟨c, fun B hB B' hB' hne hjoin => ?_⟩
  by_contra! h
  obtain ⟨c', hc'⟩ := c.exists_merge hB hB' hne hjoin h
  exact hmin c' trivial hc'

/-- Up to degree four the terminal quotient is simple, and each nonisolated block has
at least three outgoing edges. -/
theorem Terminal.final [Finite E] (hc : c.Terminal) (hd : d ≤ 4) : c.Final := by
  intro B hB B' hB' hne hjoin
  have hdis : Disjoint {v | v ∈ B} {v | v ∈ B'} :=
    disjoint_left.mpr fun v hv hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  have hsum := G.ncard_cut_union_add hdis
  have hlt := hc B hB B' hB' hne hjoin
  have hBdeg := c.cut_le B hB
  have hB'deg := c.cut_le B' hB'
  have hpos := hjoin.ncard_pos
  constructor <;> lia

end Complexity.Frontier.Multigraph.Compression

namespace Complexity.Frontier

open Finset

/-- Endpoint charging for a simple graph with degrees three or four and no adjacent
degree-three vertices. Each vertex contributes twelve and each edge contributes at most seven. -/
theorem quartic_core_density {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hlo : ∀ v, 3 ≤ H.degree v) (hhi : ∀ v, H.degree v ≤ 4)
    (hadj : ∀ u v, H.Adj u v → 7 ≤ H.degree u + H.degree v) :
    12 * Fintype.card W ≤ 7 * H.edgeFinset.card := by
  classical
  let weight (v : W) : ℕ := 7 - H.degree v
  have hweight (v : W) : H.degree v * weight v = 12 := by
    have := hlo v
    have := hhi v
    rcases (by lia : H.degree v = 3 ∨ H.degree v = 4) with h | h <;> norm_num [weight, h]
  have hfst : ∑ a : H.Dart, weight a.fst = 12 * Fintype.card W := by
    rw [← Finset.sum_fiberwise univ (fun a : H.Dart => a.fst) (fun a => weight a.fst)]
    calc ∑ v, ∑ a ∈ univ.filter (fun a : H.Dart => a.fst = v), weight a.fst
        = ∑ v, H.degree v * weight v := by
          apply sum_congr rfl
          intro v _
          rw [sum_congr rfl (fun a ha => congrArg weight (mem_filter.mp ha).2)]
          rw [sum_const, smul_eq_mul, H.dart_fst_fiber_card_eq_degree]
      _ = 12 * Fintype.card W := by simp [hweight, Nat.mul_comm]
  have hsnd : ∑ a : H.Dart, weight a.snd = ∑ a : H.Dart, weight a.fst := by
    exact Equiv.sum_comp
      (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive) (fun a => weight a.fst)
  have hsum : ∑ a : H.Dart, (weight a.fst + weight a.snd) ≤ ∑ _a : H.Dart, 7 := by
    refine sum_le_sum fun a _ => ?_
    have := hadj a.fst a.snd a.adj
    have := hhi a.fst
    have := hhi a.snd
    dsimp [weight]
    lia
  rw [sum_add_distrib, hsnd, hfst, sum_const, card_univ, smul_eq_mul,
    H.dart_card_eq_twice_card_edges] at hsum
  lia

end Complexity.Frontier

namespace Complexity.Frontier.Multigraph.Compression

open Set

variable {V E : Type*} {G : Multigraph V E} (c : Compression G 4)

end Complexity.Frontier.Multigraph.Compression
