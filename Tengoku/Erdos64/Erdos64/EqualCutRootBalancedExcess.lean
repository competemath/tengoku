import Tengoku.Erdos64.Erdos64.RootedBranches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Ambient degree excess on a finite side after removing its distinguished root.-/
def nonrootDegreeExcess
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) (r : V) : ℕ :=
  (S.erase r).sum (fun v => G.degree v) - 3 * (S.erase r).card

/-- Equal edge counts give equal degree excess for balanced closed sides.
This theorem retains `hedges` as an input under deletion-only minimality.
The stronger `GlobalEdgeMinimalCounterexample` interface supplies that input
for actual cut components in `GlobalCutEdgeBalance`; equality of excess alone
does not imply that either excess is zero.
@isnad1 id=and.12h5v.s9.1633b6d5725e from=translated src=- shape=b9fd401b vocab=1b953bf3
-/
theorem equal_cut_root_balanced_excess
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G)
    (A B : Finset V) (r : V)
    (hpartition : A ∪ B = Finset.univ)
    (hinter : A ∩ B = ({r} : Finset V))
    (hrootA : r ∈ A) (hrootB : r ∈ B)
    (hclosedA : ∀ x, x ∈ A → x ≠ r →
      ∀ y, G.Adj x y → y ∈ A)
    (hclosedB : ∀ x, x ∈ B → x ≠ r →
      ∀ y, G.Adj x y → y ∈ B)
    (hnocross : ∀ x, x ∈ A → x ≠ r →
      ∀ y, y ∈ B → y ≠ r → ¬ G.Adj x y)
    (hrootDegreeA : 2 ≤ internalDegree G A r)
    (hrootDegreeB : 2 ≤ internalDegree G B r)
    (hcard : A.card = B.card)
    (hedges :
      (G.induce (↑A : Set V)).edgeFinset.card =
        (G.induce (↑B : Set V)).edgeFinset.card) :
    internalDegree G A r = 2 ∧
      internalDegree G B r = 2 ∧
      G.degree r = 4 ∧
      (∀ v, G.Adj r v → G.degree v = 3) ∧
      nonrootDegreeExcess G A r = nonrootDegreeExcess G B r := by
  classical
  have hmin : G.minDegree ≥ 3 :=
    minimalCounterexample.vertexMinimal.isCounterexample.1
  have hside_proper : ∀ S T : Finset V,
      S ∩ T = {r} → 2 ≤ internalDegree G T r → S ≠ Finset.univ := by
    intro S T hST hT hfull
    have hnonempty : (T.filter (G.Adj r)).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < internalDegree G T r
      omega
    obtain ⟨v, hv⟩ := hnonempty
    obtain ⟨hvT, hrv⟩ := Finset.mem_filter.mp hv
    have hvS : v ∈ S := by
      rw [hfull]
      exact Finset.mem_univ v
    have hvST : v ∈ S ∩ T := Finset.mem_inter.mpr ⟨hvS, hvT⟩
    have hvr : v = r := by
      simpa only [hST, Finset.mem_singleton] using hvST
    exact hrv.ne hvr.symm
  have hproperA := hside_proper A B hinter hrootDegreeB
  have hproperB := hside_proper B A
    (by simpa only [Finset.inter_comm] using hinter) hrootDegreeA
  have hnonroot_degree : ∀ S : Finset V,
      (∀ x, x ∈ S → x ≠ r → ∀ y, G.Adj x y → y ∈ S) →
      ∀ x, x ∈ S → x ≠ r → internalDegree G S x = G.degree x := by
    intro S hclosed x hx hxr
    have hneighbors : S.filter (G.Adj x) = G.neighborFinset x := by
      ext y
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨And.right, fun hxy => ⟨hclosed x hx hxr y hxy, hxy⟩⟩
    rw [internalDegree, hneighbors, SimpleGraph.card_neighborFinset_eq_degree]
  have hroot_eq : ∀ S : Finset V, r ∈ S → S ≠ Finset.univ →
      (∀ x, x ∈ S → x ≠ r → ∀ y, G.Adj x y → y ∈ S) →
      2 ≤ internalDegree G S r → internalDegree G S r = 2 := by
    intro S hrS hproper hclosed htwo
    obtain ⟨v, hv, hlow⟩ :=
      minimalCounterexample.vertexMinimal.isSubgraphCritical S ⟨r, hrS⟩ hproper
    by_cases hvr : v = r
    · subst v
      omega
    · rw [hnonroot_degree S hclosed v hv hvr] at hlow
      have hdegree := degree_ge_three_of_minDegree_ge_three G hmin v
      omega
  have hrootEqA := hroot_eq A hrootA hproperA hclosedA hrootDegreeA
  have hrootEqB := hroot_eq B hrootB hproperB hclosedB hrootDegreeB
  have hdisj : Disjoint (A.filter (G.Adj r)) (B.filter (G.Adj r)) := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvB
    have hvAB : v ∈ A ∩ B :=
      Finset.mem_inter.mpr
        ⟨(Finset.mem_filter.mp hvA).1, (Finset.mem_filter.mp hvB).1⟩
    have hvr : v = r := by
      simpa only [hinter, Finset.mem_singleton] using hvAB
    exact (Finset.mem_filter.mp hvA).2.ne hvr.symm
  have hneighbors :
      G.neighborFinset r = A.filter (G.Adj r) ∪ B.filter (G.Adj r) := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hrv
      have hvAB : v ∈ A ∪ B := by
        rw [hpartition]
        exact Finset.mem_univ v
      rcases Finset.mem_union.mp hvAB with hvA | hvB
      · exact Or.inl ⟨hvA, hrv⟩
      · exact Or.inr ⟨hvB, hrv⟩
    · rintro (⟨_, hrv⟩ | ⟨_, hrv⟩) <;> exact hrv
  have hdegree : G.degree r = 4 := by
    have hcount := Finset.card_union_of_disjoint hdisj
    rw [← hneighbors, SimpleGraph.card_neighborFinset_eq_degree] at hcount
    change G.degree r = internalDegree G A r + internalDegree G B r at hcount
    omega
  have hhand : ∀ S : Finset V, r ∈ S →
      (∀ x, x ∈ S → x ≠ r → ∀ y, G.Adj x y → y ∈ S) →
      internalDegree G S r + (S.erase r).sum (fun v => G.degree v) =
        2 * (G.induce (↑S : Set V)).edgeFinset.card := by
    intro S hrS hclosed
    let H : SimpleGraph (↑S : Set V) := G.induce (↑S : Set V)
    have hsum_bij :
        S.sum (fun v => internalDegree G S v) =
          (Finset.univ : Finset (↑S : Set V)).sum (fun v => H.degree v) := by
      refine Finset.sum_bij (fun a ha => ⟨a, ?_⟩) ?_ ?_ ?_ ?_
      · exact ha
      · simp
      · intro a₁ ha₁ a₂ ha₂ h
        exact congrArg Subtype.val h
      · intro b hb
        exact ⟨b.1, b.2, Subtype.ext rfl⟩
      · intro a ha
        simpa only [H] using
          (degree_induce_coeFinset_eq_internalDegree G ⟨a, ha⟩).symm
    have hsum :
        S.sum (fun v => internalDegree G S v) = 2 * H.edgeFinset.card :=
      hsum_bij.trans H.sum_degrees_eq_twice_card_edges
    have hnonroot_sum :
        (S.erase r).sum (fun v => internalDegree G S v) =
          (S.erase r).sum (fun v => G.degree v) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hnonroot_degree S hclosed v
        (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
    rw [← Finset.add_sum_erase S (fun v => internalDegree G S v) hrS,
      hnonroot_sum] at hsum
    exact hsum
  have hsumA := hhand A hrootA hclosedA
  have hsumB := hhand B hrootB hclosedB
  rw [hrootEqA, hedges] at hsumA
  rw [hrootEqB] at hsumB
  have hsum_eq :
      (A.erase r).sum (fun v => G.degree v) =
        (B.erase r).sum (fun v => G.degree v) := by omega
  refine ⟨hrootEqA, hrootEqB, hdegree, ?_, ?_⟩
  · intro v hrv
    exact minimalCounterexample.neighbor_degree_eq_three_of_degree_ge_four
      (by omega) hrv
  · unfold nonrootDegreeExcess
    rw [hsum_eq, Finset.card_erase_of_mem hrootA,
      Finset.card_erase_of_mem hrootB, hcard]

end Erdos64
