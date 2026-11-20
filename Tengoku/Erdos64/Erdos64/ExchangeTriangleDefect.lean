import Tengoku.Erdos64.Erdos64.SubcubicCycleExchange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

open scoped Classical symmDiff

private theorem not_two_same_color_exchange_edges
    {V : Type u} [Fintype V] {G H K : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (hKG : K ≤ G) (hK : K.IsCycles)
    {v w w' : V} (hdegree : G.degree v ≤ 3)
    (hKnonempty : (K.neighborSet v).Nonempty) (hww' : w ≠ w')
    (hw : (H \ K).Adj v w) (hw' : (H \ K).Adj v w') : False := by
  classical
  obtain ⟨c, hc⟩ := hKnonempty
  obtain ⟨d, hcd, hd⟩ := hK.other_adj_of_adj hc
  have hwc : w ≠ c := by rintro rfl; exact hw.2 hc
  have hwd : w ≠ d := by rintro rfl; exact hw.2 hd
  have hw'c : w' ≠ c := by rintro rfl; exact hw'.2 hc
  have hw'd : w' ≠ d := by rintro rfl; exact hw'.2 hd
  have hsub : ({w, w', c, d} : Finset V) ⊆ G.neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    apply (G.mem_neighborFinset v z).mpr
    rcases hz with rfl | rfl | rfl | rfl
    · exact hHG hw.1
    · exact hHG hw'.1
    · exact hKG hc
    · exact hKG hd
  have hcard : ({w, w', c, d} : Finset V).card = 4 := by
    simp [hww', hwc, hwd, hw'c, hw'd, hcd]
  have hle := Finset.card_le_card hsub
  rw [hcard, SimpleGraph.card_neighborFinset_eq_degree] at hle
  omega

/-- At a vertex where two cycle unions agree on whether the vertex is
isolated, two distinct exchange edges have opposite colors. Only the local
ambient degree bound is needed.
@isnad1 id=iff.9h7v.s7.3e00c66ec6cb from=translated src=- shape=3a662c86 vocab=3aeabd4e
-/
theorem cycle_exchange_alternates_at_common_support
    {V : Type u} [Fintype V] {G H K : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (hKG : K ≤ G) (hH : H.IsCycles) (hK : K.IsCycles)
    {v w w' : V} (hdegree : G.degree v ≤ 3)
    (hagree : (H.neighborSet v).Nonempty ↔ (K.neighborSet v).Nonempty)
    (hww' : w ≠ w') (hw : (H ∆ K).Adj v w) (hw' : (H ∆ K).Adj v w') :
    H.Adj v w ↔ ¬H.Adj v w' := by
  change (H.Adj v w ∧ ¬K.Adj v w) ∨ (K.Adj v w ∧ ¬H.Adj v w) at hw
  change (H.Adj v w' ∧ ¬K.Adj v w') ∨ (K.Adj v w' ∧ ¬H.Adj v w') at hw'
  constructor
  · intro hvw hvw'
    have h₁ : (H \ K).Adj v w := by tauto
    have h₂ : (H \ K).Adj v w' := by tauto
    exact not_two_same_color_exchange_edges hHG hKG hK hdegree
      (hagree.mp ⟨w, hvw⟩) hww' h₁ h₂
  · intro hvw'
    by_contra hvw
    have h₁ : (K \ H).Adj v w := by tauto
    have h₂ : (K \ H).Adj v w' := by tauto
    exact not_two_same_color_exchange_edges hKG hHG hH hdegree
      (hagree.mpr ⟨w, h₁.1⟩) hww' h₁ h₂

/-- A triangle in the exchange of two cycle unions in a subcubic union
contains a support defect: a vertex used by exactly one cycle union.
In particular, an exchange triangle cannot be supported entirely on the
vertices common to both original cycles.
@isnad1 id=or.6h6v.s7.713ec356242f from=translated src=- shape=e737b428 vocab=98cd9fb4
-/
theorem cycle_exchange_triangle_has_support_defect
    {V : Type u} [Fintype V] {H K : SimpleGraph V}
    (hH : H.IsCycles) (hK : K.IsCycles)
    (hdegree : ∀ v, (H ⊔ K).degree v ≤ 3)
    {x y z : V} (hxy : (H ∆ K).Adj x y) (hyz : (H ∆ K).Adj y z)
    (hzx : (H ∆ K).Adj z x) :
    ¬((H.neighborSet x).Nonempty ↔ (K.neighborSet x).Nonempty) ∨
      ¬((H.neighborSet y).Nonempty ↔ (K.neighborSet y).Nonempty) ∨
      ¬((H.neighborSet z).Nonempty ↔ (K.neighborSet z).Nonempty) := by
  by_contra h
  push Not at h
  have hx := cycle_exchange_alternates_at_common_support
    (G := H ⊔ K) (H := H) (K := K) le_sup_left le_sup_right hH hK
    (hdegree x) h.1 hyz.ne hxy hzx.symm
  have hy := cycle_exchange_alternates_at_common_support
    (G := H ⊔ K) (H := H) (K := K) le_sup_left le_sup_right hH hK
    (hdegree y) h.2.1 hzx.ne.symm hxy.symm hyz
  have hz := cycle_exchange_alternates_at_common_support
    (G := H ⊔ K) (H := H) (K := K) le_sup_left le_sup_right hH hK
    (hdegree z) h.2.2 hxy.ne.symm hyz.symm hzx
  rw [H.adj_comm y x] at hy
  rw [H.adj_comm z y, H.adj_comm z x] at hz
  tauto

/-- To exclude triangles from an exchange, it is enough to exclude ambient
triangles at the support defects. No restriction on triangles elsewhere in
the ambient graph is imposed.
@isnad1 id=ne.7h6v.s7.728ddb52c683 from=translated src=- shape=c27e3757 vocab=5e7fabc5
-/
theorem cycle_exchange_no_triangles_of_support_defects
    {V : Type u} [Fintype V] {G H K : SimpleGraph V}
    (hHG : H ≤ G) (hKG : K ≤ G) (hH : H.IsCycles) (hK : K.IsCycles)
    (hdegree : ∀ v, (H ⊔ K).degree v ≤ 3)
    (hdefect : ∀ v, ¬((H.neighborSet v).Nonempty ↔ (K.neighborSet v).Nonempty) →
      ∀ a b, G.Adj v a → G.Adj a b → G.Adj b v → False)
    {v : V} (p : (H ∆ K).Walk v v) (_hp : p.IsCycle) : p.length ≠ 3 := by
  intro hlen
  have hxy : (H ∆ K).Adj v (p.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.adj_getVert_succ (by omega : 0 < p.length)
  have hyz : (H ∆ K).Adj (p.getVert 1) (p.getVert 2) :=
    p.adj_getVert_succ (by omega : 1 < p.length)
  have hzx : (H ∆ K).Adj (p.getVert 2) v := by
    have h := p.adj_getVert_succ (by omega : 2 < p.length)
    change (H ∆ K).Adj (p.getVert 2) (p.getVert 3) at h
    rw [← hlen, SimpleGraph.Walk.getVert_length] at h
    exact h
  have hle : H ∆ K ≤ G := symmDiff_le_sup.trans (sup_le hHG hKG)
  rcases cycle_exchange_triangle_has_support_defect hH hK hdegree hxy hyz hzx with
    hx | hy | hz
  · exact hdefect v hx _ _ (hle hxy) (hle hyz) (hle hzx)
  · exact hdefect (p.getVert 1) hy _ _ (hle hyz) (hle hzx) (hle hxy)
  · exact hdefect (p.getVert 2) hz _ _ (hle hzx) (hle hxy) (hle hyz)

/-- The eight-edge criterion only needs the vertices whose cycle membership
changes to lie on no ambient triangle. For cycles omitting one vertex each,
these support defects are among the two omitted vertices. This theorem does
not assert the existence of an eight-edge exchange or of suitable defects.
@isnad1 id=haspower.7h4v.s7.a42a5b5f9eb1 from=translated src=- shape=272e075c vocab=5b07ba85
-/
theorem hasPowerOfTwoCycle_of_eight_edge_exchange_triangle_free_defects
    {V : Type u} [Fintype V] {G H K : SimpleGraph V}
    (hHG : H ≤ G) (hKG : K ≤ G) (hH : H.IsCycles) (hK : K.IsCycles)
    (hdegree : ∀ v, (H ⊔ K).degree v ≤ 3)
    (hedges : (H ∆ K).edgeFinset.card = 8)
    (hdefect : ∀ v, ¬((H.neighborSet v).Nonempty ↔ (K.neighborSet v).Nonempty) →
      ∀ a b, G.Adj v a → G.Adj a b → G.Adj b v → False) :
    HasPowerOfTwoCycle G := by
  exact hasPowerOfTwoCycle_of_eight_edge_cycle_exchange hHG hKG hH hK hdegree hedges
    (cycle_exchange_no_triangles_of_support_defects hHG hKG hH hK hdegree hdefect)

/-- An eight-edge exchange between cycle unions with the same support
forces a dyadic cycle without excluding ambient triangles. In the
near-Hamiltonian setting this applies when both cycles omit the same vertex.
@isnad1 id=haspower.7h4v.s7.5a4aed7426a7 from=translated src=- shape=7cbe2e57 vocab=5b07ba85
-/
theorem hasPowerOfTwoCycle_of_eight_edge_exchange_same_support
    {V : Type u} [Fintype V] {G H K : SimpleGraph V}
    (hHG : H ≤ G) (hKG : K ≤ G) (hH : H.IsCycles) (hK : K.IsCycles)
    (hdegree : ∀ v, (H ⊔ K).degree v ≤ 3)
    (hedges : (H ∆ K).edgeFinset.card = 8)
    (hagree : ∀ v, (H.neighborSet v).Nonempty ↔ (K.neighborSet v).Nonempty) :
    HasPowerOfTwoCycle G := by
  apply hasPowerOfTwoCycle_of_eight_edge_exchange_triangle_free_defects
    hHG hKG hH hK hdegree hedges
  intro v hv
  exact (hv (hagree v)).elim

end Erdos64
