import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Add one new vertex adjacent exactly to the named boundary vertices.-/
def boundaryRootGraph {W : Type u} (H : SimpleGraph W) (B : Finset W) :
    SimpleGraph (Option W) where
  Adj
    | none, none => False
    | none, some w => w ∈ B
    | some w, none => w ∈ B
    | some v, some w => H.Adj v w
  symm := ⟨by
    intro v w h
    cases v <;> cases w <;> first | exact h | exact h.symm⟩
  loopless := ⟨by intro v h; cases v with
    | none => exact h
    | some w => exact H.irrefl h⟩

instance boundaryRootGraph_decidableRel
    {W : Type u} [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (B : Finset W) :
    DecidableRel (boundaryRootGraph H B).Adj := by
  intro v w
  cases v <;> cases w <;> dsimp [boundaryRootGraph] <;> infer_instance

@[simp] theorem boundaryRootGraph_adj_some_some
    {W : Type u} (H : SimpleGraph W) (B : Finset W) (v w : W) :
    (boundaryRootGraph H B).Adj (some v) (some w) ↔ H.Adj v w := Iff.rfl

@[simp] theorem boundaryRootGraph_adj_none_some
    {W : Type u} (H : SimpleGraph W) (B : Finset W) (w : W) :
    (boundaryRootGraph H B).Adj none (some w) ↔ w ∈ B := Iff.rfl

@[simp] theorem boundaryRootGraph_adj_some_none
    {W : Type u} (H : SimpleGraph W) (B : Finset W) (w : W) :
    (boundaryRootGraph H B).Adj (some w) none ↔ w ∈ B := Iff.rfl

/-- Each boundary vertex gains exactly one new neighbor.-/
theorem boundaryRootGraph_degree_some
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (B : Finset W) (w : W) :
    (boundaryRootGraph H B).degree (some w) =
      H.degree w + if w ∈ B then 1 else 0 := by
  classical
  by_cases hw : w ∈ B
  · have hfin : (boundaryRootGraph H B).neighborFinset (some w) =
        insert none ((H.neighborFinset w).map Function.Embedding.some) := by
      ext v
      cases v <;> simp [SimpleGraph.mem_neighborFinset, hw]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hfin,
      Finset.card_insert_of_notMem (by simp), Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree]
    simp [hw]
  · have hfin : (boundaryRootGraph H B).neighborFinset (some w) =
        (H.neighborFinset w).map Function.Embedding.some := by
      ext v
      cases v <;> simp [SimpleGraph.mem_neighborFinset, hw]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hfin, Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree]
    simp [hw]

/-- The added root has one neighbor for each boundary vertex.-/
theorem boundaryRootGraph_degree_none
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (B : Finset W) :
    (boundaryRootGraph H B).degree none = B.card := by
  classical
  have hfin : (boundaryRootGraph H B).neighborFinset none =
      B.map Function.Embedding.some := by
    ext v
    cases v <;> simp [SimpleGraph.mem_neighborFinset]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hfin, Finset.card_map]

/-- Deleting the added root recovers the original graph exactly.-/
def boundaryRootDeletedIso
    {W : Type u} (H : SimpleGraph W) (B : Finset W) :
    ((boundaryRootGraph H B).induce {v : Option W | v ≠ none}) ≃g H where
  toFun v := v.1.get (Option.ne_none_iff_isSome.mp v.2)
  invFun w := ⟨some w, by simp⟩
  left_inv v := Subtype.ext (Option.some_get _)
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩
    change v ≠ none at hv
    change w ≠ none at hw
    cases v with
    | none => exact (hv rfl).elim
    | some a =>
      cases w with
      | none => exact (hw rfl).elim
      | some b => rfl

@[simp] theorem boundaryRootDeletedIso_some
    {W : Type u} (H : SimpleGraph W) (B : Finset W) (w : W) :
    boundaryRootDeletedIso H B ⟨some w, by simp⟩ = w := rfl

/-- A cycle avoiding the added root projects to an original simple cycle,
without changing its length.-/
theorem boundaryRoot_cycle_avoiding_root
    {W : Type u} {H : SimpleGraph W} {B : Finset W} {v : Option W}
    (c : (boundaryRootGraph H B).Walk v v) (hc : c.IsCycle)
    (havoid : none ∉ c.support) :
    ∃ w, ∃ q : H.Walk w w, q.IsCycle ∧ q.length = c.length := by
  have hinside : ∀ z, z ∈ c.support → z ∈ {z : Option W | z ≠ none} := by
    intro z hz hzn
    exact havoid (hzn ▸ hz)
  let c' := c.induce {z : Option W | z ≠ none} hinside
  have hc' : c'.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f :=
      (SimpleGraph.Embedding.induce {z : Option W | z ≠ none}).toHom)
    have hmap := hc
    rw [← c.map_induce hinside] at hmap
    exact hmap
  let e := boundaryRootDeletedIso H B
  refine ⟨_, c'.map e.toHom, hc'.map e.injective, ?_⟩
  rw [SimpleGraph.Walk.length_map]
  have hlen := congrArg SimpleGraph.Walk.length (c.map_induce hinside)
  exact (SimpleGraph.Walk.length_map
    (SimpleGraph.Embedding.induce {z : Option W | z ≠ none}).toHom c').symm.trans hlen

end Erdos64
