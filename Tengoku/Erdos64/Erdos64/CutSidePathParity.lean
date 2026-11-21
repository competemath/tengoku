import Tengoku.Erdos64.Erdos64.CutSideDyadicEar
import Tengoku.Erdos64.Erdos64.ExactTwoPortResidual
import Tengoku.Erdos64.Erdos64.TwoPortDefectBookkeeping
import Tengoku.Seed.Combinatorics.SimpleGraph.DegreeSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A finite graph with exactly two specified even-degree vertices and odd
degrees elsewhere has even order, by the handshaking lemma.
@isnad1 id=even.4h4v.s7.e1859fa048a1 from=translated src=- shape=2b4ee639 vocab=daf76e80
-/
theorem even_card_of_two_even_degree_vertices
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (x y : V) (hxy : x ≠ y)
    (hx : Even (G.degree x)) (hy : Even (G.degree y))
    (hother : ∀ v, v ≠ x → v ≠ y → Odd (G.degree v)) :
    Even (Fintype.card V) := by
  classical
  have hfilter : Finset.univ.filter (fun v => Odd (G.degree v)) =
      (Finset.univ.erase x).erase y := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hv
      refine ⟨?_, ?_, trivial⟩
      · intro h
        subst v
        exact (Nat.not_odd_iff_even.mpr hy) hv
      · intro h
        subst v
        exact (Nat.not_odd_iff_even.mpr hx) hv
    · rintro ⟨hvy, hvx, _⟩
      exact hother v hvx hvy
  have heven := G.even_card_odd_degree_vertices
  rw [hfilter] at heven
  have hxcard := Finset.card_erase_add_one (Finset.mem_univ x)
  have hycard := Finset.card_erase_add_one
    (show y ∈ Finset.univ.erase x by simp [hxy.symm])
  rw [Finset.card_univ] at hxcard
  obtain ⟨k, hk⟩ := heven
  exact ⟨k + 1, by omega⟩

/-- Removing the two incidences to a common external root changes two odd
degrees to even degrees. Hence an exact two-port side whose ambient degrees
are all odd has even cardinality. No minimal-counterexample premise is used.
@isnad1 id=even.7h6v.s7.2ca334135a36 from=translated src=- shape=9abb7872 vocab=5c3592e9
-/
theorem exact_two_port_side_card_even_of_odd_degrees
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y)
    (hboundary : ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact : ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hodd : ∀ v, v ∈ D → Odd (G.degree v)) :
    Even D.card := by
  classical
  let H := G.induce (↑D : Set V)
  let xx : (↑D : Set V) := ⟨x, hx⟩
  let yy : (↑D : Set V) := ⟨y, hy⟩
  have hdeg : ∀ v : (↑D : Set V),
      H.degree v + (if G.Adj v.1 r then 1 else 0) = G.degree v.1 := by
    intro v
    rw [degree_induce_coeFinset_eq_internalDegree]
    exact internalDegree_add_root_indicator_eq_degree D r hr hboundary v.2
  have hxroot : G.Adj x r := (hexact x hx).mpr (Or.inl rfl)
  have hyroot : G.Adj y r := (hexact y hy).mpr (Or.inr rfl)
  have hxEven : Even (H.degree xx) := by
    have h : H.degree xx + 1 = G.degree x := by
      simpa only [xx, hxroot, ↓reduceIte] using hdeg xx
    obtain ⟨k, hk⟩ := hodd x hx
    exact ⟨k, by omega⟩
  have hyEven : Even (H.degree yy) := by
    have h : H.degree yy + 1 = G.degree y := by
      simpa only [yy, hyroot, ↓reduceIte] using hdeg yy
    obtain ⟨k, hk⟩ := hodd y hy
    exact ⟨k, by omega⟩
  have hother : ∀ v, v ≠ xx → v ≠ yy → Odd (H.degree v) := by
    intro v hvx hvy
    have hvr : ¬G.Adj v.1 r := by
      intro h
      rcases (hexact v.1 v.2).mp h with h | h
      · exact hvx (Subtype.ext h)
      · exact hvy (Subtype.ext h)
    have h := hdeg v
    simp only [hvr, ↓reduceIte, Nat.add_zero] at h
    rw [h]
    exact hodd v.1 v.2
  have heven := even_card_of_two_even_degree_vertices H xx yy
    (fun h => hxy (congrArg Subtype.val h)) hxEven hyEven hother
  simpa using heven

/-- Native cut-side balance gives exactly two ports, so odd ambient degrees
force even order on either side. Cubic sides are an immediate special case.
@isnad1 id=even.3h5v.s7.3d821e4d91e7 from=translated src=- shape=01653e92 vocab=707d44ab
-/
theorem MinimalCounterexample.rootDeleted_cut_side_card_even_of_odd_degrees
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    (hodd : ∀ v, v ∈ rootDeletedComponentCarrier G r C → Odd (G.degree v)) :
    Even (rootDeletedComponentCarrier G r C).card := by
  classical
  let := Fintype.ofFinite ((G.induce {v : V | v ≠ r}).ConnectedComponent)
  have hcard := (M.rootDeleted_two_components_exact_balanced r C D hCD).2.2.1
  obtain ⟨x, y, hx, hy, hxy, hrx, hry, hports⟩ :=
    rootDeletedComponent_twoPort_attachment_exact r C hcard
  have hboundary : ∀ v, v ∈ rootDeletedComponentCarrier G r C →
      ∀ w, w ∉ rootDeletedComponentCarrier G r C → G.Adj v w → w = r := by
    intro v hv w hw hvw
    exact ((rootDeletedComponent_boundary r M.isConnected C).1 v hv w hvw).resolve_left hw
  have hexact : ∀ v, v ∈ rootDeletedComponentCarrier G r C →
      (G.Adj v r ↔ v = x ∨ v = y) := by
    intro v hv
    refine ⟨hports v hv, ?_⟩
    rintro (rfl | rfl)
    · exact hrx.symm
    · exact hry.symm
  exact exact_two_port_side_card_even_of_odd_degrees
    (rootDeletedComponentCarrier G r C) r x y
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2 hx hy hxy
    hboundary hexact hodd

/-- A simple even-length path cannot cover a finite carrier of even order.
@isnad1 id=ex.4h6v.s6.9464a5c7570b from=translated src=- shape=a4c5ed83 vocab=f1997dda
-/
theorem exists_vertex_outside_even_path_of_even_card
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (D : Finset V) (hD : Even D.card) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (heven : Even p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ D) :
    ∃ v, v ∈ D ∧ v ∉ p.support := by
  classical
  by_contra hnot
  have hcover : ∀ v, v ∈ D → v ∈ p.support := by
    intro v hv
    by_contra hvp
    exact hnot ⟨v, hv, hvp⟩
  have heq : p.support.toFinset = D := by
    ext v
    simpa using ⟨hinside v, hcover v⟩
  have hcard : D.card = p.length + 1 := by
    rw [← heq, List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  obtain ⟨a, ha⟩ := hD
  obtain ⟨b, hb⟩ := heven
  omega

/-- All odd ambient degrees in a cut side force every simple even-length
path inside that side to omit a vertex. In particular this applies to any
cubic side and to any simple dyadic port path.
@isnad1 id=ex.6h8v.s7.e3416aa3d04e from=translated src=- shape=d156d326 vocab=37c5761c
-/
theorem MinimalCounterexample.rootDeleted_even_path_external_vertex_of_odd_degrees
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    (hodd : ∀ v, v ∈ rootDeletedComponentCarrier G r C → Odd (G.degree v))
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (heven : Even p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C) :
    ∃ v, v ∈ rootDeletedComponentCarrier G r C ∧ v ∉ p.support := by
  exact exists_vertex_outside_even_path_of_even_card
    (rootDeletedComponentCarrier G r C)
    (M.rootDeleted_cut_side_card_even_of_odd_degrees r C D hCD hodd)
    p hp heven hinside

/-- In an all-odd-degree cut side, a simple even port path always has a
fresh dyadic ear. The off-path vertex required by component extraction is
produced by parity, rather than assumed.
@isnad1 id=ex.9h8v.s8.a65de3a667ad from=translated src=- shape=5f7a4c48 vocab=b31a196f
-/
theorem MinimalCounterexample.rootDeleted_even_port_path_dyadic_ear_of_odd_degrees
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    (hodd : ∀ v, v ∈ rootDeletedComponentCarrier G r C → Odd (G.degree v))
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath) (heven : Even p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v ∈ p.support → v = a ∨ v = b) ∧
      (∀ v, v ∈ ear.support → v ∈ rootDeletedComponentCarrier G r C) := by
  obtain ⟨v, hv, hvp⟩ :=
    M.rootDeleted_even_path_external_vertex_of_odd_degrees r C D hCD hodd
      p hp heven hinside
  exact M.rootDeleted_cut_side_dyadic_ear_of_external_vertex r C D hCD
    hxy hrx hry p hinside v hv hvp

/-- If an even port path spans its cut side, that side has an even-degree
ambient vertex of degree at least four. Edge-minimality makes both ports
cubic, so the forced vertex is internal. Otherwise an actual dyadic ear is
produced. This narrows the spanning case but does not exclude it.
@isnad1 id=or.8h8v.s8.78fd475a273b from=translated src=- shape=cfd63106 vocab=a9c0f5da
-/
theorem EdgeMinimalCounterexample.rootDeleted_even_port_path_ear_or_spanning_even_degree_vertex
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath) (heven : Even p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C) :
    (∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v ∈ p.support → v = a ∨ v = b) ∧
      (∀ v, v ∈ ear.support → v ∈ rootDeletedComponentCarrier G r C)) ∨
    ((∀ v, v ∈ rootDeletedComponentCarrier G r C → v ∈ p.support) ∧
      ∃ v, v ∈ rootDeletedComponentCarrier G r C ∧ v ≠ x ∧ v ≠ y ∧
        Even (G.degree v) ∧ 4 ≤ G.degree v) := by
  classical
  by_cases hexternal : ∃ v, v ∈ rootDeletedComponentCarrier G r C ∧ v ∉ p.support
  · obtain ⟨v, hv, hvp⟩ := hexternal
    exact Or.inl (M.vertexMinimal.rootDeleted_cut_side_dyadic_ear_of_external_vertex
      r C D hCD hxy hrx hry p hinside v hv hvp)
  right
  have hcover : ∀ v, v ∈ rootDeletedComponentCarrier G r C → v ∈ p.support := by
    intro v hv
    by_contra hvp
    exact hexternal ⟨v, hv, hvp⟩
  have hnotodd : ¬∀ v, v ∈ rootDeletedComponentCarrier G r C → Odd (G.degree v) := by
    intro hodd
    exact hexternal (M.vertexMinimal.rootDeleted_even_path_external_vertex_of_odd_degrees
      r C D hCD hodd p hp heven hinside)
  push Not at hnotodd
  obtain ⟨v, hv, hvodd⟩ := hnotodd
  have hveven : Even (G.degree v) := Nat.not_odd_iff_even.mp hvodd
  have hmin := degree_ge_three_of_minDegree_ge_three G M.vertexMinimal.isCounterexample.1 v
  have hhigh : 4 ≤ G.degree v := by
    obtain ⟨k, hk⟩ := hveven
    omega
  let := Fintype.ofFinite ((G.induce {v : V | v ≠ r}).ConnectedComponent)
  have hrootdeg := (M.vertexMinimal.rootDeleted_two_components_exact_balanced r C D hCD).2.2.2.2
  have hxdeg := M.neighbor_degree_eq_three_of_degree_ge_four (by omega : 4 ≤ G.degree r) hrx
  have hydeg := M.neighbor_degree_eq_three_of_degree_ge_four (by omega : 4 ≤ G.degree r) hry
  refine ⟨hcover, v, hv, ?_, ?_, hveven, hhigh⟩
  · intro h
    subst v
    omega
  · intro h
    subst v
    omega

end Erdos64
