import Tengoku.Erdos64.Erdos64.OneDefectDyadicForcing
import Tengoku.Erdos64.Erdos64.RootedBranches
import Tengoku.Erdos64.Erdos64.RootDeletedNoDyadicTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Vertices of a finite carrier that have a neighbor outside it.-/
noncomputable def carrierBoundaryVertices
    {V : Type u} [Fintype V] (G : SimpleGraph V) (D : Finset V) :
    Finset {v : V // v ∈ D} := by
  classical
  exact Finset.univ.filter (fun v => ∃ w, w ∉ D ∧ G.Adj v.1 w)

/--
@isnad1 id=iff.0h4v.s7.ede136750180 from=translated src=- shape=a38832ac vocab=b57f1a1b
-/
@[simp] theorem mem_carrierBoundaryVertices
    {V : Type u} [Fintype V] (G : SimpleGraph V) (D : Finset V)
    (v : {v : V // v ∈ D}) :
    v ∈ carrierBoundaryVertices G D ↔ ∃ w, w ∉ D ∧ G.Adj v.1 w := by
  classical
  simp [carrierBoundaryVertices]

/-- If every carrier vertex has at most one external neighbor, its induced
degree loses exactly one at the boundary and otherwise remains unchanged.
@isnad1 id=eq.1h4v.s9.09abbbc5d00f from=translated src=- shape=87defc93 vocab=e3ffc10e
-/
theorem carrier_degree_add_boundary_indicator
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V)
    (hsingle : ∀ v, v ∈ D → ∀ a, a ∉ D → ∀ b, b ∉ D →
      G.Adj v a → G.Adj v b → a = b)
    (v : {v : V // v ∈ D}) :
    (G.induce (↑D : Set V)).degree v +
      (if v ∈ carrierBoundaryVertices G D then 1 else 0) = G.degree v.1 := by
  classical
  let O := (G.neighborFinset v.1).filter (fun w => w ∉ D)
  have hinside : (G.neighborFinset v.1).filter (fun w => w ∈ D) =
      D.filter (G.Adj v.1) := by
    ext w
    simp [and_comm]
  have houtside : O.card = if v ∈ carrierBoundaryVertices G D then 1 else 0 := by
    by_cases hv : v ∈ carrierBoundaryVertices G D
    · obtain ⟨a, ha, hva⟩ := (mem_carrierBoundaryVertices G D v).mp hv
      have hO : O = {a} := by
        ext b
        simp only [O, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hvb, hb⟩
          exact hsingle v.1 v.2 b hb a ha hvb hva
        · rintro rfl
          exact ⟨hva, ha⟩
      simp [hv, hO]
    · have hO : O = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨hva, ha⟩ := Finset.mem_filter.mp ha
        exact hv ((mem_carrierBoundaryVertices G D v).mpr
          ⟨a, ha, (G.mem_neighborFinset v.1 a).mp hva⟩)
      simp [hv, hO]
  have hsplit := (G.neighborFinset v.1).card_filter_add_card_filter_not
    (fun w => w ∈ D)
  rw [hinside, show ((G.neighborFinset v.1).filter (fun w => ¬w ∈ D)).card =
      O.card from rfl, houtside] at hsplit
  simpa only [degree_induce_coeFinset_eq_internalDegree, internalDegree,
    SimpleGraph.card_neighborFinset_eq_degree] using hsplit

/-- A sufficiently small nonempty carrier cannot have fewer than two
boundary vertices when each loses at most one incidence. Otherwise it has
at most one degree-two defect, and its rooted double contradicts minimality.
@isnad1 id=le.4h3v.s7.495cb6d8ab42 from=translated src=- shape=1b3dd2f7 vocab=7bab5ccf
-/
theorem MinimalCounterexample.small_carrier_boundary_card_ge_two
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (D : Finset V) (hD : D.Nonempty)
    (hsingle : ∀ v, v ∈ D → ∀ a, a ∉ D → ∀ b, b ∉ D →
      G.Adj v a → G.Adj v b → a = b)
    (hsize : 2 * D.card + 1 < Fintype.card V) :
    2 ≤ (carrierBoundaryVertices G D).card := by
  classical
  let B := carrierBoundaryVertices G D
  let H := G.induce (↑D : Set V)
  by_contra hsmall
  have hBcard : B.card ≤ 1 := by
    change (carrierBoundaryVertices G D).card ≤ 1
    omega
  obtain ⟨y, hy⟩ : ∃ y : {v : V // v ∈ D}, ∀ v, v ∈ B → v = y := by
    by_cases hB : B.Nonempty
    · obtain ⟨y, hy⟩ := hB
      exact ⟨y, fun v hv => (Finset.card_le_one.mp hBcard) v hv y hy⟩
    · obtain ⟨a, ha⟩ := hD
      refine ⟨⟨a, ha⟩, ?_⟩
      intro v hv
      exact (hB ⟨v, hv⟩).elim
  have hdeg : ∀ v : {v : V // v ∈ D},
      H.degree v + (if v ∈ B then 1 else 0) = G.degree v.1 :=
    carrier_degree_add_boundary_indicator D hsingle
  have hydeg : 2 ≤ H.degree y := by
    have h := hdeg y
    have hmin := degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 y.1
    split_ifs at h <;> omega
  have hother : ∀ v, v ≠ y → 3 ≤ H.degree v := by
    intro v hv
    have hvB : v ∉ B := fun h => hv (hy v h)
    have h := hdeg v
    have hmin := degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 v.1
    simp only [hvB, ↓reduceIte, Nat.add_zero] at h
    omega
  have horder : 2 * Fintype.card {v : V // v ∈ D} - 1 < Fintype.card V := by
    simpa using (show 2 * D.card - 1 < Fintype.card V by omega)
  have hyes := M.one_defect_small_has_dyadic_cycle y hydeg hother horder
  exact (not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle
    M.isCounterexample.2) hyes

end Erdos64
