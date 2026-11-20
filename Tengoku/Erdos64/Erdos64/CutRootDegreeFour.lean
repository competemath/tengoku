import Tengoku.Erdos64.Erdos64.MinimalCounterexampleBalancedSides

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Two disjoint nonempty closed sides meeting only through a root have exactly
 two root attachments each in a vertex-minimal counterexample. Consequently the
 root has degree four. The closure hypotheses are stated as one-port boundary
 conditions, so no degree, attachment-count, cardinality, or edge-count
 premises are needed.
@isnad1 id=and.9h5v.s8.8f7053c2dc40 from=translated src=- shape=219e3224 vocab=b8cd9dac
-/
theorem MinimalCounterexample.two_closed_sides_root_degree_four
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D E : Finset V) (r : V)
    (hD : D.Nonempty) (hE : E.Nonempty)
    (hrD : r ∉ D) (hrE : r ∉ E)
    (hdisj : Disjoint D E)
    (hcover : insert r (D ∪ E) = Finset.univ)
    (hboundaryD :
      ∀ u, u ∈ D → ∀ v, v ∉ D → G.Adj u v → v = r)
    (hboundaryE :
      ∀ u, u ∈ E → ∀ v, v ∉ E → G.Adj u v → v = r) :
    (D.filter (G.Adj r)).card = 2 ∧
      (E.filter (G.Adj r)).card = 2 ∧
      G.degree r = 4 := by
  classical
  have exists_root_neighbor : ∀ (K : Finset V), K.Nonempty →
      (r ∉ K) →
      (∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = r) →
      ∃ z, z ∈ K ∧ G.Adj r z := by
    intro K hK hrK hboundary
    by_contra hnone
    have hclosed : ∀ u, u ∈ K → ∀ v, G.Adj u v → v ∈ K := by
      intro u hu v huv
      by_contra hv
      have hvr := hboundary u hu v hv huv
      exact hnone ⟨u, hu, by simpa only [hvr] using huv.symm⟩
    have hwalk : ∀ {a b : V}, G.Walk a b → a ∈ K → b ∈ K := by
      intro a b p
      induction p with
      | nil => exact fun ha => ha
      | cons hab p ih => exact fun ha => ih (hclosed _ ha _ hab)
    obtain ⟨a, ha⟩ := hK
    obtain ⟨p⟩ := M.isConnected.preconnected a r
    exact hrK (hwalk p ha)
  have two_attach : ∀ (K : Finset V), K.Nonempty →
      (r ∉ K) →
      (∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = r) →
      2 ≤ (K.filter (G.Adj r)).card := by
    intro K hK hrK hboundary
    obtain ⟨z, hzK, hrz⟩ := exists_root_neighbor K hK hrK hboundary
    obtain ⟨t, htK, hrt, htz⟩ :=
      M.exists_second_onePort_neighbor K r z hrK hzK hrz hboundary
    have hpair : ({z, t} : Finset V) ⊆ K.filter (G.Adj r) := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hzK, hrz⟩
      · exact Finset.mem_filter.mpr ⟨htK, hrt⟩
    have hpaircard : ({z, t} : Finset V).card = 2 := by
      simp [htz.symm]
    exact hpaircard ▸ Finset.card_le_card hpair
  have root_lower_D : 2 ≤ (D.filter (G.Adj r)).card :=
    two_attach D hD hrD hboundaryD
  have root_lower_E : 2 ≤ (E.filter (G.Adj r)).card :=
    two_attach E hE hrE hboundaryE
  have houtsideD : ∃ e, e ∉ insert r D := by
    obtain ⟨e, he⟩ := hE
    refine ⟨e, ?_⟩
    simp only [Finset.mem_insert]
    intro hor
    rcases hor with her | heD
    · exact hrE (her ▸ he)
    · exact (Finset.disjoint_left.mp hdisj) heD he
  have houtsideE : ∃ d, d ∉ insert r E := by
    obtain ⟨d, hd⟩ := hD
    refine ⟨d, ?_⟩
    simp only [Finset.mem_insert]
    intro hor
    rcases hor with hdr | hdE
    · exact hrD (hdr ▸ hd)
    · exact (Finset.disjoint_left.mp hdisj) hd hdE
  have side_root_le_two : ∀ (K : Finset V), K.Nonempty →
      (r ∉ K) →
      (∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = r) →
      (∃ e, e ∉ insert r K) →
      (K.filter (G.Adj r)).card ≤ 2 := by
    intro K hK hrK hboundary houtside
    let S : Finset V := insert r K
    have hS_nonempty : S.Nonempty := by
      exact ⟨r, Finset.mem_insert_self r K⟩
    have hS_proper : S ≠ (Finset.univ : Finset V) := by
      obtain ⟨e, he⟩ := houtside
      intro hS
      have heS : e ∈ S := by
        rw [hS]
        exact Finset.mem_univ e
      exact he (by simpa [S] using heS)
    have hclosed : ∀ x, x ∈ S → x ≠ r →
        ∀ y, G.Adj x y → y ∈ S := by
      intro x hx hxr y hxy
      have hxK : x ∈ K := (Finset.mem_insert.mp hx).resolve_left hxr
      by_cases hyK : y ∈ K
      · exact Finset.mem_insert.mpr (Or.inr hyK)
      · exact Finset.mem_insert.mpr (Or.inl (hboundary x hxK y hyK hxy))
    obtain ⟨v, hvS, hvle⟩ := M.isSubgraphCritical S hS_nonempty hS_proper
    by_cases hvr : v = r
    · subst v
      have hfilter : S.filter (G.Adj r) = K.filter (G.Adj r) := by
        ext y
        constructor
        · intro hy
          rcases Finset.mem_filter.mp hy with ⟨hyS, hry⟩
          rcases Finset.mem_insert.mp hyS with hyr | hyK
          · exact (hry.ne hyr.symm).elim
          · exact Finset.mem_filter.mpr ⟨hyK, hry⟩
        · intro hy
          exact Finset.mem_filter.mpr ⟨
            Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mp hy).1),
            (Finset.mem_filter.mp hy).2⟩
      rw [internalDegree, hfilter] at hvle
      exact hvle
    · have hv_internal : internalDegree G S v = G.degree v := by
        have hneighbors : S.filter (G.Adj v) = G.neighborFinset v := by
          ext y
          simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          exact ⟨And.right, fun hvy =>
            ⟨hclosed v hvS hvr y hvy, hvy⟩⟩
        rw [internalDegree, hneighbors,
          SimpleGraph.card_neighborFinset_eq_degree]
      have hmin : 3 ≤ G.degree v :=
        degree_ge_three_of_minDegree_ge_three G
          M.isCounterexample.1 v
      rw [hv_internal] at hvle
      omega
  have root_upper_D : (D.filter (G.Adj r)).card ≤ 2 :=
    side_root_le_two D hD hrD hboundaryD houtsideD
  have root_upper_E : (E.filter (G.Adj r)).card ≤ 2 :=
    side_root_le_two E hE hrE hboundaryE houtsideE
  have hrootD : (D.filter (G.Adj r)).card = 2 := by omega
  have hrootE : (E.filter (G.Adj r)).card = 2 := by omega
  have hdisj_filter : Disjoint (D.filter (G.Adj r)) (E.filter (G.Adj r)) := by
    apply Finset.disjoint_left.mpr
    intro v hvD hvE
    exact (Finset.disjoint_left.mp hdisj)
      (Finset.mem_filter.mp hvD).1 (Finset.mem_filter.mp hvE).1
  have hneighbors : G.neighborFinset r =
      D.filter (G.Adj r) ∪ E.filter (G.Adj r) := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union,
      Finset.mem_filter]
    constructor
    · intro hrv
      have hvcover : v ∈ insert r (D ∪ E) := by
        rw [hcover]
        exact Finset.mem_univ v
      rcases Finset.mem_insert.mp hvcover with hvr | hvDE
      · exact (hrv.ne hvr.symm).elim
      · rcases Finset.mem_union.mp hvDE with hvD | hvE
        · exact Or.inl ⟨hvD, hrv⟩
        · exact Or.inr ⟨hvE, hrv⟩
    · rintro (⟨_, hrv⟩ | ⟨_, hrv⟩) <;> exact hrv
  have hcount := Finset.card_union_of_disjoint hdisj_filter
  rw [← hneighbors, SimpleGraph.card_neighborFinset_eq_degree] at hcount
  refine ⟨hrootD, hrootE, ?_⟩
  omega

/-- Edge-minimality upgrades the cut degree-four certificate to cubicity at
all neighbors of the root.
@isnad1 id=and.9h5v.s8.785152ee0408 from=translated src=- shape=2ce2fd1a vocab=a1865d46
-/
theorem EdgeMinimalCounterexample.two_closed_sides_root_degree_four_cubic
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G)
    (D E : Finset V) (r : V)
    (hD : D.Nonempty) (hE : E.Nonempty)
    (hrD : r ∉ D) (hrE : r ∉ E)
    (hdisj : Disjoint D E)
    (hcover : insert r (D ∪ E) = Finset.univ)
    (hboundaryD :
      ∀ u, u ∈ D → ∀ v, v ∉ D → G.Adj u v → v = r)
    (hboundaryE :
      ∀ u, u ∈ E → ∀ v, v ∉ E → G.Adj u v → v = r) :
    (D.filter (G.Adj r)).card = 2 ∧
      (E.filter (G.Adj r)).card = 2 ∧
      G.degree r = 4 ∧
      (∀ v, G.Adj r v → G.degree v = 3) := by
  obtain ⟨hDtwo, hEtwo, hroot⟩ :=
    M.vertexMinimal.two_closed_sides_root_degree_four D E r hD hE hrD hrE
      hdisj hcover hboundaryD hboundaryE
  refine ⟨hDtwo, hEtwo, hroot, ?_⟩
  intro v hrv
  exact M.neighbor_degree_eq_three_of_degree_ge_four
    (by omega) hrv

end Erdos64
