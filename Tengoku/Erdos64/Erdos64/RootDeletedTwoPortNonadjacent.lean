import Tengoku.Erdos64.Erdos64.RootDeletedTwoPortPath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A walk between distinct nonadjacent vertices cannot have length zero or
    one.
@isnad1 id=lt.2h5v.s5.a183f3b5c29c from=translated src=- shape=4066b9eb vocab=586a4f3d
-/
theorem one_lt_length_of_ne_of_not_adj
    {V : Type u} {G : SimpleGraph V} {a b : V} {p : G.Walk a b}
    (hab : a ≠ b) (hnadj : ¬ G.Adj a b) :
    1 < p.length := by
  by_contra hnot
  have hle : p.length ≤ 1 := Nat.le_of_not_gt hnot
  have hcases : p.length = 0 ∨ p.length = 1 := by omega
  rcases hcases with hzero | hone
  · exact hab (SimpleGraph.Walk.eq_of_length_eq_zero hzero)
  · exact hnadj (SimpleGraph.Walk.adj_of_length_eq_one hone)

/-- If every distinct pair of root-attached vertices in the component is
    explicitly nonadjacent, the extracted component path has length greater
    than one.  Nonadjacency is a premise here, not a consequence of degree or
    criticality assumptions.
@isnad1 id=ex.2h4v.s8.722dab7c54ca from=translated src=- shape=cc0166a0 vocab=b8e86835
-/
theorem rootDeletedComponent_twoPort_path_of_nonadjacent
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hcard : (rootDeletedComponentAttachments G r C).card = 2)
    (hnonadj : ∀ a b,
      a ∈ rootDeletedComponentCarrier G r C →
      b ∈ rootDeletedComponentCarrier G r C →
      G.Adj r a → G.Adj r b →
      a ≠ b → ¬ G.Adj a b) :
    ∃ a b : V, ∃ p : G.Walk a b,
      a ≠ b ∧
      a ∈ rootDeletedComponentCarrier G r C ∧
      b ∈ rootDeletedComponentCarrier G r C ∧
      G.Adj r a ∧ G.Adj r b ∧
      p.IsPath ∧
      (∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C) ∧
      r ∉ p.support ∧ 1 < p.length := by
  obtain ⟨a, b, p, hab, ha, hb, hra, hrb, hp, hinside, hroot, _hpos⟩ :=
    rootDeletedComponent_twoPort_path r C hcard
  refine ⟨a, b, p, hab, ha, hb, hra, hrb, hp, hinside, hroot, ?_⟩
  exact one_lt_length_of_ne_of_not_adj hab
    (hnonadj a b ha hb hra hrb hab)

end Erdos64
