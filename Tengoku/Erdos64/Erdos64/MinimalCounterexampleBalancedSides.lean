import Tengoku.Erdos64.Erdos64.MinimalCounterexampleBridgeless

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Every nonempty side whose external neighbors are confined to one root
contains at least half of the other vertices of a minimal counterexample.
The two root neighbors needed for doubling follow from connectedness and
bridgelessness; they are not additional hypotheses.
@isnad1 id=le.4h4v.s6.47467018f944 from=translated src=- shape=fd751d05 vocab=222721a1
-/
theorem MinimalCounterexample.onePort_side_card_bound
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r : V)
    (hD : D.Nonempty) (hr : r ∉ D)
    (hboundary :
      ∀ u, u ∈ D → ∀ v, v ∉ D → G.Adj u v → v = r) :
    Fintype.card V ≤ 2 * D.card + 1 := by
  classical
  have hneighbor : ∃ z, z ∈ D ∧ G.Adj r z := by
    by_contra hnone
    have hclosed : ∀ u, u ∈ D → ∀ v, G.Adj u v → v ∈ D := by
      intro u hu v huv
      by_contra hv
      have hvr := hboundary u hu v hv huv
      exact hnone ⟨u, hu, by simpa only [hvr] using huv.symm⟩
    have hwalk : ∀ {a b : V}, G.Walk a b → a ∈ D → b ∈ D := by
      intro a b p
      induction p with
      | nil => exact fun ha => ha
      | cons hab p ih => exact fun ha => ih (hclosed _ ha _ hab)
    obtain ⟨a, ha⟩ := hD
    obtain ⟨p⟩ := M.isConnected.preconnected a r
    exact hr (hwalk p ha)
  obtain ⟨z, hz, hrz⟩ := hneighbor
  obtain ⟨t, ht, hrt, htz⟩ :=
    M.exists_second_onePort_neighbor D r z hr hz hrz hboundary
  let S : Finset V := insert r D
  let root : {v : V // v ∈ S} := ⟨r, Finset.mem_insert_self r D⟩
  have hclosed : ∀ u, u ∈ S → u ≠ root.val →
      ∀ v, G.Adj u v → v ∈ S := by
    intro u hu hur v huv
    have huD : u ∈ D := (Finset.mem_insert.mp hu).resolve_left hur
    by_cases hvD : v ∈ D
    · exact Finset.mem_insert.mpr (Or.inr hvD)
    · exact Finset.mem_insert.mpr
        (Or.inl (hboundary u huD v hvD huv))
  have hpair : ({z, t} : Finset V) ⊆ S.filter (G.Adj r) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · subst v
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr (Or.inr hz), hrz⟩
    · subst v
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr (Or.inr ht), hrt⟩
  have hpaircard : ({z, t} : Finset V).card = 2 := by
    simp [htz.symm]
  have hroot : 2 ≤ internalDegree G S root.val := by
    have hle := Finset.card_le_card hpair
    simpa only [hpaircard, internalDegree] using hle
  have hScard : S.card = D.card + 1 := Finset.card_insert_of_notMem hr
  by_contra hbound
  have hsmall : 2 * S.card - 1 < Fintype.card V := by omega
  exact M.not_exists_strictly_smaller
    (strict_double_of_closed_side M.isCounterexample S root
      hclosed hroot hsmall)

/-- Two disjoint nonempty sides with the same sole external root must be
equally large and exhaust every vertex other than that root. In particular,
a third nonempty disjoint side is impossible.
@isnad1 id=and.8h5v.s7.54f243a09ac5 from=translated src=- shape=8288adc9 vocab=71765636
-/
theorem MinimalCounterexample.two_onePort_sides_balanced
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D E : Finset V) (r : V)
    (hD : D.Nonempty) (hE : E.Nonempty)
    (hrD : r ∉ D) (hrE : r ∉ E)
    (hdisj : Disjoint D E)
    (hboundaryD :
      ∀ u, u ∈ D → ∀ v, v ∉ D → G.Adj u v → v = r)
    (hboundaryE :
      ∀ u, u ∈ E → ∀ v, v ∉ E → G.Adj u v → v = r) :
    D.card = E.card ∧ insert r (D ∪ E) = Finset.univ := by
  classical
  have hDbound := M.onePort_side_card_bound D r hD hrD hboundaryD
  have hEbound := M.onePort_side_card_bound E r hE hrE hboundaryE
  have hrU : r ∉ D ∪ E := by
    simpa only [Finset.mem_union, not_or] using And.intro hrD hrE
  have hcard : (insert r (D ∪ E)).card = D.card + E.card + 1 := by
    rw [Finset.card_insert_of_notMem hrU, Finset.card_union_of_disjoint hdisj]
  have hle : D.card + E.card + 1 ≤ Fintype.card V := by
    have h := Finset.card_le_card (Finset.subset_univ (insert r (D ∪ E)))
    simpa only [hcard, Finset.card_univ] using h
  have hDE : D.card = E.card := by omega
  have hN : Fintype.card V = D.card + E.card + 1 := by omega
  refine ⟨hDE, ?_⟩
  ext v
  simp only [Finset.mem_univ, iff_true]
  by_contra hv
  have hle' :=
    Finset.card_le_card (Finset.subset_univ (insert v (insert r (D ∪ E))))
  rw [Finset.card_insert_of_notMem hv, hcard, Finset.card_univ] at hle'
  omega

end Erdos64
