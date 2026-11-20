import Tengoku.Erdos64.Erdos64.PentagramEarHullPrivateAttachment
import Tengoku.Erdos64.Erdos64.PentagramEarHullExteriorComponents

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

open PentagramEarHull

universe u v

variable {V : Type u} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Disjoint exterior carriers cannot share a private `b` index. Only the
exterior-neighbor and neighbor-classification parts of the witnesses are needed.
@isnad1 id=ne.4h7v.s7.59e1c654ca3d from=translated src=- shape=0478f827 vocab=5d5fe012
-/
theorem private_b_indices_ne_of_disjoint
    (H : PentagramEarHull G) {D E : Finset V}
    (hdisjoint : Disjoint D E)
    (hext : ∀ w, w ∈ D → w ∉ H.hull)
    {i j : Fin 5}
    (hD : ∃ w, w ∈ D ∧ G.Adj (H.bVertex i) w)
    (hE : ∀ w, G.Adj (H.bVertex j) w →
      w = H.aVertex j ∨ w = H.aVertex (j + 2) ∨ w ∈ E) :
    i ≠ j := by
  intro hij
  subst j
  obtain ⟨w, hwD, hwAdj⟩ := hD
  rcases hE w hwAdj with hwa | hwb | hwE
  · have hwHull : w ∈ H.hull := by
      rw [hwa]
      exact Or.inl (Or.inr ⟨i, rfl⟩)
    exact hext w hwD hwHull
  · have hwHull : w ∈ H.hull := by
      rw [hwb]
      exact Or.inl (Or.inr ⟨i + 2, rfl⟩)
    exact hext w hwD hwHull
  · exact (Finset.disjoint_left.mp hdisjoint) hwD hwE

/-- A finite pairwise-disjoint family of nonempty closed exterior carriers has
at most five members, by choosing the private attachments supplied by criticality.
@isnad1 id=le.6h5v.s7.22175b2dc088 from=translated src=- shape=7eec3390 vocab=13794830
-/
theorem closed_exterior_family_card_le_five
    (H : PentagramEarHull G)
    (hmin : 3 ≤ G.minDegree)
    (hcrit : IsSubgraphCritical G)
    {ι : Type v} [Fintype ι]
    (D : ι → Finset V)
    (hnonempty : ∀ a, (D a).Nonempty)
    (hext : ∀ a w, w ∈ D a → w ∉ H.hull)
    (hclosed : ∀ a x, x ∈ D a → ∀ y,
      G.Adj x y → y ∈ D a ∨ y ∈ H.hull)
    (hpair : Pairwise (fun a b => Disjoint (D a) (D b))) :
    Fintype.card ι ≤ 5 := by
  classical
  have hwitness (a : ι) :=
    private_b_of_closed_exterior H hmin hcrit (D a)
      (hnonempty a) (hext a) (hclosed a)
  choose f hf using hwitness
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact (private_b_indices_ne_of_disjoint H (hpair hne)
      (hext a) (hf a).2.2 (hf b).2.1) hab
  calc
    Fintype.card ι ≤ Fintype.card (Fin 5) :=
      Fintype.card_le_of_injective f hinj
    _ = 5 := by simp

/-- There are at most five actual connected components outside the hull.
@isnad1 id=le.2h3v.s6.24588ffb3bac from=translated src=- shape=ad9312c1 vocab=4c27d134
-/
theorem PentagramEarHull.exteriorComponents_card_le_five
    (H : PentagramEarHull G)
    (hmin : 3 ≤ G.minDegree)
    (hcrit : IsSubgraphCritical G) :
    H.exteriorComponents.card ≤ 5 := by
  classical
  letI : Fintype H.exteriorGraph.ConnectedComponent := Fintype.ofFinite _
  have hcard := closed_exterior_family_card_le_five H hmin hcrit
    H.exteriorComponentCarrier
    H.exteriorComponentCarrier_nonempty
    (fun C w hw => H.exteriorComponentCarrier_not_mem_hull C hw)
    (fun C x hx y hxy => H.exteriorComponentCarrier_adj_closure C hx hxy)
    H.exteriorComponentCarrier_pairwise_disjoint
  simpa only [PentagramEarHull.exteriorComponents, Finset.card_univ] using hcard

end Erdos64
