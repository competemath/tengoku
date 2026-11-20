import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u v

/-- Realize each edge of `H` by a two-edge path in `G`, using distinct middle
vertices which are disjoint from the images of the vertices of `H`.-/
structure TwoStepEmbedding {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  vertex : W ↪ V
  middle : H.edgeSet ↪ V
  disjoint : ∀ w e, vertex w ≠ middle e
  adj : ∀ {a b} (h : H.Adj a b),
    G.Adj (vertex a) (middle ⟨s(a, b), h⟩) ∧
      G.Adj (middle ⟨s(a, b), h⟩) (vertex b)

namespace TwoStepEmbedding

variable {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (E : TwoStepEmbedding H G)

/-- Replace every edge of a walk by its specified two-edge path.-/
def lift (E : TwoStepEmbedding H G) {a b : W} :
    H.Walk a b → G.Walk (E.vertex a) (E.vertex b)
  | .nil => .nil
  | .cons h p => .cons (E.adj h).1 (.cons (E.adj h).2 (lift E p))

@[simp] theorem length_lift {a b : W} (p : H.Walk a b) :
    (E.lift p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [lift, SimpleGraph.Walk.length_cons, ih]; omega

@[simp] theorem vertex_mem_support_lift {a b : W} (p : H.Walk a b) (w : W) :
    E.vertex w ∈ (E.lift p).support ↔ w ∈ p.support := by
  induction p with
  | nil => simp [lift, E.vertex.injective.eq_iff]
  | cons h p ih =>
    simp only [lift, SimpleGraph.Walk.support_cons, List.mem_cons, ih,
      E.vertex.injective.eq_iff, E.disjoint, false_or]

@[simp] theorem middle_mem_support_lift {a b : W} (p : H.Walk a b)
    (e : H.edgeSet) : E.middle e ∈ (E.lift p).support ↔ e.1 ∈ p.edges := by
  induction p with
  | nil => simp [lift, (E.disjoint _ _).symm]
  | cons h p ih =>
    simp only [lift, SimpleGraph.Walk.support_cons, List.mem_cons,
      SimpleGraph.Walk.edges_cons, ih, (E.disjoint _ _).symm, false_or,
      E.middle.injective.eq_iff, Subtype.ext_iff]

/-- Two-step replacement preserves simplicity of paths.-/
theorem isPath_lift {a b : W} {p : H.Walk a b} (hp : p.IsPath) :
    (E.lift p).IsPath := by
  induction p with
  | nil => exact SimpleGraph.Walk.IsPath.nil
  | @cons a b c h p ih =>
    obtain ⟨hp, ha⟩ := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
    apply (SimpleGraph.Walk.cons_isPath_iff _ _).mpr
    constructor
    · apply (SimpleGraph.Walk.cons_isPath_iff _ _).mpr
      refine ⟨ih hp, ?_⟩
      rw [E.middle_mem_support_lift]
      exact fun he => ha (p.fst_mem_support_of_mem_edges he)
    · simp only [SimpleGraph.Walk.support_cons, List.mem_cons,
        E.disjoint, E.vertex_mem_support_lift, false_or]
      exact ha

/-- A simple cycle lifts to a simple cycle of twice its original length.-/
theorem isCycle_lift {a : W} {p : H.Walk a a} (hp : p.IsCycle) :
    (E.lift p).IsCycle := by
  have hlen := hp.three_le_length
  cases p with
  | nil => simp at hp
  | cons h p =>
    obtain ⟨hpath, hedge⟩ := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hp
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · change (SimpleGraph.Walk.cons (E.adj h).2 (E.lift p)).IsPath
      apply (SimpleGraph.Walk.cons_isPath_iff _ _).mpr
      exact ⟨E.isPath_lift hpath, by simpa only [E.middle_mem_support_lift] using hedge⟩
    · rw [E.length_lift]
      omega

include E in
/-- Uniform subdivision by two preserves the existence of a dyadic cycle.-/
theorem hasPowerOfTwoCycle (hH : HasPowerOfTwoCycle H) : HasPowerOfTwoCycle G := by
  obtain ⟨k, a, p, hk, hp, hlen⟩ := hH
  refine ⟨k + 1, E.vertex a, E.lift p, by omega, E.isCycle_lift hp, ?_⟩
  rw [E.length_lift, hlen, pow_succ, Nat.mul_comm]

end TwoStepEmbedding
end Erdos64
