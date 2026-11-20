import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Tengoku.Seed.Combinatorics.SimpleGraph.Paths

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A path inside an induced carrier avoiding the three displayed vertices
    lifts to an ambient simple path with the same avoidance property.-/
theorem separated_third_neighbor_path
    {V : Type u} {G : SimpleGraph V} {D : Set V}
    {r x y z w : V}
    (hDroot : ∀ v, v ∈ D → v ≠ r)
    (hDxy : ∀ v, v ∈ D → v ≠ x ∧ v ≠ y)
    (C : (G.induce D).ConnectedComponent)
    (hzD : z ∈ D) (hwD : w ∈ D)
    (hzC : (⟨z, hzD⟩ : D) ∈ C)
    (hwC : (⟨w, hwD⟩ : D) ∈ C) :
    ∃ p : G.Walk z w, p.IsPath ∧
      (∀ v, v ∈ p.support → v ≠ r ∧ v ≠ x ∧ v ≠ y) := by
  obtain ⟨q, hq⟩ := C.connected_toSimpleGraph.exists_isPath
    (⟨⟨z, hzD⟩, hzC⟩ : C) (⟨⟨w, hwD⟩, hwC⟩ : C)
  let e : C.toSimpleGraph →g G :=
    { toFun := fun v => v.1.1
      map_rel' := fun h => h }
  have he : Function.Injective e := by
    intro a b hab
    change a.1.1 = b.1.1 at hab
    exact Subtype.ext (Subtype.ext hab)
  let p : G.Walk z w := q.map e
  have hp : p.IsPath :=
    (SimpleGraph.Walk.isPath_map_iff_of_injective (f := e) he).mpr hq
  have havoid : ∀ v, v ∈ p.support → v ≠ r ∧ v ≠ x ∧ v ≠ y := by
    intro v hv
    change v ∈ (q.map e).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨u, _hu, rfl⟩ := List.mem_map.mp hv
    exact ⟨hDroot u.1.1 u.1.2, hDxy u.1.1 u.1.2⟩
  exact ⟨p, hp, havoid⟩

end Erdos64
