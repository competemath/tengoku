import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Two distinct root neighbors in an induced-connected finite side admit a
    simple path through the side.  The path is exported in the ambient graph,
    with its exact length and root avoidance exposed for later spectrum
    arguments.  No arithmetic condition on that length is asserted.-/
theorem exists_simple_marked_root_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) (r x y : V)
    (hconn : (G.induce (↑S : Set V)).Connected)
    (hrS : r ∉ S)
    (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (hrx : G.Adj r x) (hry : G.Adj r y) :
    ∃ n : ℕ, ∃ p : G.Walk x y,
      p.IsPath ∧ p.length = n ∧ 0 < n ∧
      r ∉ p.support ∧ G.Adj r x ∧ G.Adj r y := by
  classical
  obtain ⟨q, hq⟩ := hconn.exists_isPath
    (⟨x, hxS⟩ : (↑S : Set V)) (⟨y, hyS⟩ : (↑S : Set V))
  let e : G.induce (↑S : Set V) →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  let p : G.Walk x y := q.map e
  have hp : p.IsPath := by
    exact (SimpleGraph.Walk.isPath_map_iff_of_injective
      (f := e) Subtype.val_injective).mpr hq
  have hqpos : 0 < q.length := by
    have hqzero : q.length ≠ 0 := by
      intro hzero
      have hxy' :
          (⟨x, hxS⟩ : (↑S : Set V)) = (⟨y, hyS⟩ : (↑S : Set V)) :=
        SimpleGraph.Walk.eq_of_length_eq_zero hzero
      exact hxy (congrArg Subtype.val hxy')
    omega
  have hrootavoid : r ∉ p.support := by
    intro hrp
    change r ∈ (q.map e).support at hrp
    rw [SimpleGraph.Walk.support_map] at hrp
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hrp
    exact hrS z.property
  refine ⟨q.length, p, hp, ?_, ?_, hrootavoid, hrx, hry⟩
  · rw [SimpleGraph.Walk.length_map]
  · exact hqpos

end Erdos64
