/-
OEIS A347722, bridge lemma 2: every star forest is the edge set of a good idempotent map.

Construction. For a vertex `v` of degree 1 let `nbr S v` be the other endpoint of its unique
edge. The map `gmap S` fixes every vertex of degree `≠ 1`; a vertex `v` of degree 1 whose
neighbour has degree `≠ 1` is sent to that neighbour (the centre of its star); and on an isolated
edge (both endpoints of degree 1) both endpoints are sent to the smaller one.
-/
import Tengoku.OeisLean.OeisLean.A347722.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A347722.exists_good_of_star` (it only prints; the queue checks the axioms of every declaration). -/

namespace A347722.Bridge2

variable {n : ℕ} {S : Finset (Finset (Fin n))}

/--
@isnad1 id=ne.2h4v.s6.2be530ed1e37 from=translated src=- shape=8da70aee vocab=2f128cbf
-/
theorem pair_ne (hS : S ⊆ verts n) {x y : Fin n} (h : {x, y} ∈ S) : x ≠ y := by
  rintro rfl
  have := hS h
  simp [verts, Finset.mem_powersetCard] at this

/--
@isnad1 id=ex.2h3v.s6.8e285fcba4a3 from=translated src=- shape=87a23bb5 vocab=2f128cbf
-/
theorem edge_form (hS : S ⊆ verts n) {e : Finset (Fin n)} (h : e ∈ S) :
    ∃ x y, x ≠ y ∧ e = {x, y} := by
  have := hS h
  rw [verts, Finset.mem_powersetCard] at this
  exact Finset.card_eq_two.mp this.2

/--
@isnad1 id=eq.5h5v.s6.4cebc4197da0 from=translated src=- shape=a0578086 vocab=ae9bf85f
-/
theorem edge_unique {v : Fin n} (hv : deg S v = 1) {e e' : Finset (Fin n)} (he : e ∈ S)
    (hve : v ∈ e) (he' : e' ∈ S) (hve' : v ∈ e') : e = e' := by
  have h : (S.filter fun e => v ∈ e).card ≤ 1 := le_of_eq hv
  exact Finset.card_le_one.mp h e (Finset.mem_filter.mpr ⟨he, hve⟩) e'
    (Finset.mem_filter.mpr ⟨he', hve'⟩)

/--
@isnad1 id=ex.2h3v.s6.5bec67912735 from=translated src=- shape=1e503ca1 vocab=7e5cca93
-/
theorem exists_nbr (hS : S ⊆ verts n) {v : Fin n} (hv : deg S v = 1) :
    ∃ u, u ≠ v ∧ {v, u} ∈ S := by
  have h : 0 < deg S v := by omega
  unfold deg at h
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter] at he
  obtain ⟨he, hve⟩ := he
  obtain ⟨x, y, hxy, rfl⟩ := edge_form hS he
  rw [Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with hvx | hvy
  · subst hvx
    exact ⟨y, hxy.symm, he⟩
  · subst hvy
    exact ⟨x, hxy, by rw [Finset.pair_comm]; exact he⟩

/--
@isnad1 id=eq.4h5v.s6.c27672b6034a from=translated src=- shape=7b29a732 vocab=cb9c50b7
-/
theorem pair_unique {v u w : Fin n} (hv : deg S v = 1) (hu : {v, u} ∈ S) (hw : {v, w} ∈ S)
    (huv : u ≠ v) : u = w := by
  have h := edge_unique hv hu (Finset.mem_insert_self _ _) hw (Finset.mem_insert_self _ _)
  have hmem : u ∈ ({v, w} : Finset (Fin n)) := by rw [← h]; simp
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact absurd h1 huv
  · exact h1

/-- A vertex of degree `≠ 1` lying on an edge lies on a second edge.
@isnad1 id=ex.3h4v.s7.d5eefb7d6d17 from=translated src=- shape=72e3000f vocab=7e5cca93
-/
theorem exists_other (hS : S ⊆ verts n) {v u : Fin n} (hu : {v, u} ∈ S) (hv : deg S v ≠ 1) :
    ∃ w, w ≠ v ∧ w ≠ u ∧ {v, w} ∈ S := by
  by_contra hcon
  apply hv
  have hfil : (S.filter fun e => v ∈ e) = {{v, u}} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hve⟩
      obtain ⟨x, y, hxy, rfl⟩ := edge_form hS he
      rw [Finset.mem_insert, Finset.mem_singleton] at hve
      rcases hve with hvx | hvy
      · subst hvx
        by_contra hne
        exact hcon ⟨y, hxy.symm, fun h => hne (by rw [h]), he⟩
      · subst hvy
        by_contra hne
        exact hcon ⟨x, hxy, fun h => hne (by rw [h, Finset.pair_comm]),
          by rw [Finset.pair_comm]; exact he⟩
    · rintro rfl
      exact ⟨hu, Finset.mem_insert_self _ _⟩
  unfold deg
  rw [hfil, Finset.card_singleton]

/--
@isnad1 id=or.2h4v.s6.a4836822d245 from=translated src=- shape=3dcfca48 vocab=1887537f
-/
theorem star_pair (h : Star S) {x y : Fin n} (hxy : {x, y} ∈ S) :
    deg S x = 1 ∨ deg S y = 1 := by
  obtain ⟨v, hv, hd⟩ := h _ hxy
  rw [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact Or.inl hd
  · exact Or.inr hd

/-- The other endpoint of an edge at `v` (meaningful when `deg S v = 1`).-/
noncomputable def nbr (S : Finset (Finset (Fin n))) (v : Fin n) : Fin n :=
  if hv : ∃ u, u ≠ v ∧ {v, u} ∈ S then Classical.choose hv else v

/--
@isnad1 id=and.2h3v.s6.b4740d7ca9c0 from=translated src=- shape=30ee4dd1 vocab=cfe16ed7
-/
theorem nbr_spec (hS : S ⊆ verts n) {v : Fin n} (hv : deg S v = 1) :
    nbr S v ≠ v ∧ {v, nbr S v} ∈ S := by
  have h := exists_nbr hS hv
  unfold nbr
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/--
@isnad1 id=eq.3h4v.s6.c1f350141c72 from=translated src=- shape=3012cfba vocab=cfe16ed7
-/
theorem nbr_eq (hS : S ⊆ verts n) {v u : Fin n} (hv : deg S v = 1) (hu : {v, u} ∈ S) :
    nbr S v = u :=
  pair_unique hv (nbr_spec hS hv).2 hu (nbr_spec hS hv).1

/--
@isnad1 id=eq.3h3v.s6.febab3593da3 from=translated src=- shape=d3852bf9 vocab=8613b705
-/
theorem nbr_nbr (hS : S ⊆ verts n) {v : Fin n} (hv : deg S v = 1)
    (h2 : deg S (nbr S v) = 1) : nbr S (nbr S v) = v :=
  nbr_eq hS h2 (by rw [Finset.pair_comm]; exact (nbr_spec hS hv).2)

/-- The good idempotent map attached to a star forest.-/
noncomputable def gmap (S : Finset (Finset (Fin n))) (v : Fin n) : Fin n :=
  if deg S v = 1 then (if deg S (nbr S v) = 1 then min v (nbr S v) else nbr S v) else v

/--
@isnad1 id=eq.1h3v.s4.cf3f29b7b856 from=translated src=- shape=7cb6a910 vocab=582f1682
-/
theorem gmap_of_ne {v : Fin n} (h : deg S v ≠ 1) : gmap S v = v := by
  unfold gmap
  rw [ite_eq_right h]

/--
@isnad1 id=eq.2h3v.s5.0ebc4b0fc963 from=translated src=- shape=bf3f25af vocab=35412017
-/
theorem gmap_of_one_ne {v : Fin n} (h : deg S v = 1) (h2 : deg S (nbr S v) ≠ 1) :
    gmap S v = nbr S v := by
  unfold gmap
  rw [ite_eq_left h, ite_eq_right h2]

/--
@isnad1 id=eq.2h3v.s5.8ba2e0c9139c from=translated src=- shape=367b1ea4 vocab=4529c174
-/
theorem gmap_of_one_one {v : Fin n} (h : deg S v = 1) (h2 : deg S (nbr S v) = 1) :
    gmap S v = min v (nbr S v) := by
  unfold gmap
  rw [ite_eq_left h, ite_eq_left h2]

/--
@isnad1 id=and.1h3v.s5.cf3ee3ea5109 from=translated src=- shape=bcff1b22 vocab=35412017
-/
theorem gmap_ne {v : Fin n} (h : gmap S v ≠ v) : deg S v = 1 ∧ gmap S v = nbr S v := by
  have h1 : deg S v = 1 := by
    by_contra h1
    exact h (gmap_of_ne h1)
  refine ⟨h1, ?_⟩
  by_cases h2 : deg S (nbr S v) = 1
  · rw [gmap_of_one_one h1 h2] at h ⊢
    rcases le_total v (nbr S v) with hle | hle
    · exact absurd (min_eq_left hle) h
    · exact min_eq_right hle
  · exact gmap_of_one_ne h1 h2

/--
@isnad1 id=idem.1h2v.s5.98aec67849ff from=translated src=- shape=d0821795 vocab=18b8d05d
-/
theorem gmap_idem (hS : S ⊆ verts n) : Idem (gmap S) := by
  intro v
  by_cases hfix : gmap S v = v
  · rw [hfix, hfix]
  · obtain ⟨h1, h2⟩ := gmap_ne hfix
    rw [h2]
    by_cases h3 : deg S (nbr S v) = 1
    · have hmin := gmap_of_one_one h1 h3
      rw [h2] at hmin
      have hle : nbr S v ≤ v := hmin.le.trans (min_le_left _ _)
      rw [gmap_of_one_one h3 (by rw [nbr_nbr hS h1 h3]; exact h1), nbr_nbr hS h1 h3]
      exact min_eq_left hle
    · exact gmap_of_ne h3

/--
@isnad1 id=not.2h3v.s5.7512951302e2 from=translated src=- shape=c1312349 vocab=6adc6b10
-/
theorem gmap_not_bad (hS : S ⊆ verts n) (hst : Star S) (c : Fin n) : ¬ BadAt (gmap S) c := by
  rintro ⟨-, x, hxc, hgx, hall⟩
  have hne : gmap S x ≠ x := by rw [hgx]; exact (ne_of_lt hxc).symm
  obtain ⟨h1, h2⟩ := gmap_ne hne
  have hnc : nbr S x = c := h2.symm.trans hgx
  have hc : deg S c ≠ 1 := by
    intro hc
    have hmin := gmap_of_one_one h1 (by rw [hnc]; exact hc)
    rw [hgx, hnc] at hmin
    have hle : c ≤ x := hmin.le.trans (min_le_left _ _)
    exact absurd hxc (not_lt.mpr hle)
  have hxS : {c, x} ∈ S := by
    have := (nbr_spec hS h1).2
    rw [hnc, Finset.pair_comm] at this
    exact this
  obtain ⟨w, hwc, hwx, hw⟩ := exists_other hS hxS hc
  have hdw : deg S w = 1 := (star_pair hst hw).resolve_left hc
  have hnw : nbr S w = c := nbr_eq hS hdw (by rw [Finset.pair_comm]; exact hw)
  have hgw : gmap S w = c := by rw [gmap_of_one_ne hdw (by rw [hnw]; exact hc), hnw]
  rcases hall w hgw with h | h
  · exact hwx h
  · exact hwc h

/--
@isnad1 id=iff.0h3v.s6.992b9407d776 from=translated src=- shape=48bfc5a3 vocab=4b177410
-/
theorem mem_edgeSet {g : Fin n → Fin n} {e : Finset (Fin n)} :
    e ∈ edgeSet g ↔ ∃ v, g v ≠ v ∧ {v, g v} = e := by
  unfold edgeSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, (Finset.mem_filter.mp hv).2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

/--
@isnad1 id=mem.3h4v.s7.b6c9cd6e046a from=translated src=- shape=1567110f vocab=06e915aa
-/
theorem pair_mem_edgeSet (hS : S ⊆ verts n) {x y : Fin n} (hxy : {x, y} ∈ S)
    (hx : deg S x = 1) : {x, y} ∈ edgeSet (gmap S) := by
  have hne := pair_ne hS hxy
  have hnx : nbr S x = y := nbr_eq hS hx hxy
  rw [mem_edgeSet]
  by_cases hy : deg S y = 1
  · have hny : nbr S y = x := nbr_eq hS hy (by rw [Finset.pair_comm]; exact hxy)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hg : gmap S y = x := by
        rw [gmap_of_one_one hy (by rw [hny]; exact hx), hny]
        exact min_eq_right hlt.le
      exact ⟨y, by rw [hg]; exact hne, by rw [hg, Finset.pair_comm]⟩
    · have hg : gmap S x = y := by
        rw [gmap_of_one_one hx (by rw [hnx]; exact hy), hnx]
        exact min_eq_right hlt.le
      exact ⟨x, by rw [hg]; exact hne.symm, by rw [hg]⟩
  · have hg : gmap S x = y := by rw [gmap_of_one_ne hx (by rw [hnx]; exact hy), hnx]
    exact ⟨x, by rw [hg]; exact hne.symm, by rw [hg]⟩

end A347722.Bridge2

namespace A347722

/-- Every star forest `S` on `Fin n` is the edge set of a good idempotent map: leaves are sent to
the centre of their star, and on an isolated edge the larger endpoint is sent to the smaller.
@isnad1 id=ex.2h2v.s5.b25b710e6e7a from=translated src=- shape=6fc4abae vocab=56181425
-/
theorem exists_good_of_star {n : ℕ} (S : Finset (Finset (Fin n))) (hS : S ⊆ verts n)
    (h : Star S) : ∃ g : Fin n → Fin n, Good g ∧ edgeSet g = S := by
  refine ⟨Bridge2.gmap S, ⟨Bridge2.gmap_idem hS, Bridge2.gmap_not_bad hS h⟩, ?_⟩
  ext e
  rw [Bridge2.mem_edgeSet]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h1, h2⟩ := Bridge2.gmap_ne hv
    rw [h2]
    exact (Bridge2.nbr_spec hS h1).2
  · intro he
    obtain ⟨x, y, -, rfl⟩ := Bridge2.edge_form hS he
    rw [← Bridge2.mem_edgeSet]
    rcases Bridge2.star_pair h he with hx | hy
    · exact Bridge2.pair_mem_edgeSet hS he hx
    · rw [Finset.pair_comm]
      exact Bridge2.pair_mem_edgeSet hS (by rw [Finset.pair_comm]; exact he) hy

end A347722

