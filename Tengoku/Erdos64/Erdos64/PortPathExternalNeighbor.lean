import Tengoku.Erdos64.Erdos64.CutSideEarCoverage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The predecessor and successor of an internal vertex on a simple path
are distinct neighbors belonging to the path support.-/
theorem internal_path_vertex_two_neighbors
    {V : Type u} {G : SimpleGraph V} {x y s : V}
    (p : G.Walk x y) (hp : p.IsPath) (hs : s ∈ p.support)
    (hsx : s ≠ x) (hsy : s ≠ y) :
    ∃ a b, a ≠ b ∧ G.Adj s a ∧ G.Adj s b ∧ a ∈ p.support ∧ b ∈ p.support := by
  obtain ⟨i, hi, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hs
  have hi0 : i ≠ 0 := by
    intro h
    exact hsx (by simpa [h] using hi.symm)
  have hin : i ≠ p.length := by
    intro h
    exact hsy (by simpa [h] using hi.symm)
  have hipos : 0 < i := by omega
  have hilt : i < p.length := by omega
  refine ⟨p.getVert (i - 1), p.getVert (i + 1), ?_, ?_, ?_,
    p.getVert_mem_support _, p.getVert_mem_support _⟩
  · intro h
    have heq := hp.getVert_injOn (by change i - 1 ≤ p.length; omega)
      (by change i + 1 ≤ p.length; omega) h
    omega
  · have hadj := p.adj_getVert_succ (i := i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega, hi] at hadj
    exact hadj.symm
  · simpa only [hi] using p.adj_getVert_succ hilt

/-- Every vertex of a nontrivial simple port path has two distinct neighbors
in the path support together with the external common root.-/
theorem port_path_vertex_two_retained_neighbors
    {V : Type u} {G : SimpleGraph V} {r x y s : V}
    (p : G.Walk x y) (hp : p.IsPath) (hxy : x ≠ y)
    (hrp : r ∉ p.support) (hrx : G.Adj r x) (hry : G.Adj r y)
    (hs : s ∈ p.support) :
    ∃ a b, a ≠ b ∧ G.Adj s a ∧ G.Adj s b ∧
      (a = r ∨ a ∈ p.support) ∧ (b = r ∨ b ∈ p.support) := by
  have hlen : 0 < p.length := by
    by_contra h
    exact hxy (SimpleGraph.Walk.eq_of_length_eq_zero (by omega : p.length = 0))
  by_cases hsx : s = x
  · subst s
    refine ⟨r, p.getVert 1, ?_, hrx.symm, ?_, Or.inl rfl,
      Or.inr (p.getVert_mem_support 1)⟩
    · intro h
      exact hrp (h.symm ▸ p.getVert_mem_support 1)
    · simpa using p.adj_getVert_succ (i := 0) hlen
  by_cases hsy : s = y
  · subst s
    have hmem : p.reverse.getVert 1 ∈ p.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
        p.reverse.getVert_mem_support 1
    refine ⟨r, p.reverse.getVert 1, ?_, hry.symm, ?_, Or.inl rfl, Or.inr hmem⟩
    · intro h
      exact hrp (h.symm ▸ hmem)
    · simpa using p.reverse.adj_getVert_succ (i := 0) (by simpa using hlen)
  obtain ⟨a, b, hab, hsa, hsb, ha, hb⟩ :=
    internal_path_vertex_two_neighbors p hp hs hsx hsy
  exact ⟨a, b, hab, hsa, hsb, Or.inr ha, Or.inr hb⟩

/-- At a cubic vertex, two distinct neighbors in a retained set leave at
most one neighbor outside that set.-/
theorem cubic_vertex_external_neighbors_eq
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {s a b v w : V} (S : Set V) (hsdeg : G.degree s = 3)
    (hab : a ≠ b) (hsa : G.Adj s a) (hsb : G.Adj s b)
    (ha : a ∈ S) (hb : b ∈ S)
    (hv : v ∉ S) (hw : w ∉ S) (hsv : G.Adj s v) (hsw : G.Adj s w) :
    v = w := by
  classical
  have hamem : a ∈ G.neighborFinset s := (G.mem_neighborFinset s a).mpr hsa
  have hbmem : b ∈ (G.neighborFinset s).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset s b).mpr hsb⟩
  have hcard : (((G.neighborFinset s).erase a).erase b).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem hamem,
      SimpleGraph.card_neighborFinset_eq_degree, hsdeg]
  have hvmem : v ∈ ((G.neighborFinset s).erase a).erase b := by
    apply Finset.mem_erase.mpr
    refine ⟨fun h => hv (h ▸ hb), ?_⟩
    exact Finset.mem_erase.mpr ⟨fun h => hv (h ▸ ha),
      (G.mem_neighborFinset s v).mpr hsv⟩
  have hwmem : w ∈ ((G.neighborFinset s).erase a).erase b := by
    apply Finset.mem_erase.mpr
    refine ⟨fun h => hw (h ▸ hb), ?_⟩
    exact Finset.mem_erase.mpr ⟨fun h => hw (h ▸ ha),
      (G.mem_neighborFinset s w).mpr hsw⟩
  exact (Finset.card_le_one.mp hcard) v hvmem w hwmem

/-- Every cubic vertex of a simple port path has at most one neighbor
outside both the path and its common root, including the two ports.-/
theorem cubic_port_path_external_neighbors_eq
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {r x y : V} (p : G.Walk x y) (hp : p.IsPath) (hxy : x ≠ y)
    (hrp : r ∉ p.support) (hrx : G.Adj r x) (hry : G.Adj r y)
    (s : V) (hs : s ∈ p.support) (hsdeg : G.degree s = 3)
    (v : V) (hvp : v ∉ p.support) (hvr : v ≠ r)
    (w : V) (hwp : w ∉ p.support) (hwr : w ≠ r)
    (hsv : G.Adj s v) (hsw : G.Adj s w) : v = w := by
  obtain ⟨a, b, hab, hsa, hsb, ha, hb⟩ :=
    port_path_vertex_two_retained_neighbors p hp hxy hrp hrx hry hs
  exact cubic_vertex_external_neighbors_eq {z | z = r ∨ z ∈ p.support}
    hsdeg hab hsa hsb ha hb (fun h => h.elim hvr hvp) (fun h => h.elim hwr hwp)
    hsv hsw

/-- A cubic vertex of a simple cut-side port path has at most one neighbor
in any specified carrier outside the path. This derives the
unique attachment premise used by boundary-root avoidance.-/
theorem cut_side_port_path_external_neighbors_eq
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (r : V) (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath)
    (hinside : ∀ z, z ∈ p.support → z ∈ rootDeletedComponentCarrier G r C)
    (K : Finset V)
    (hK : ∀ z, z ∈ K → z ∈ rootDeletedComponentCarrier G r C ∧ z ∉ p.support)
    (s : V) (hs : s ∈ p.support) (hsdeg : G.degree s = 3)
    (v : V) (hv : v ∈ K) (w : V) (hw : w ∈ K)
    (hsv : G.Adj s v) (hsw : G.Adj s w) : v = w := by
  have hrC := (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
  have hrp : r ∉ p.support := fun h => hrC (hinside r h)
  have hvr : v ≠ r := by
    intro h
    subst v
    exact hrC (hK r hv).1
  have hwr : w ≠ r := by
    intro h
    subst w
    exact hrC (hK r hw).1
  exact cubic_port_path_external_neighbors_eq p hp hxy hrp hrx hry
    s hs hsdeg v (hK v hv).2 hvr w (hK w hw).2 hwr hsv hsw

end Erdos64
