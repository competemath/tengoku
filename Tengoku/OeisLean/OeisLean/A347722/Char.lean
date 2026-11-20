/-
OEIS A347722: characterisation of irredundant sets of the triangular graph `T(n)`.

A set `S` of edges of `K_n` is irredundant in `T(n)` iff it is a star forest leaving some vertex
uncovered, or a perfect matching (`irredundant_iff`).
-/
import Tengoku.OeisLean.OeisLean.A347722.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A347722.irredundant_iff` (it only prints; the queue checks the axioms of every declaration). -/

namespace A347722.Char

variable {n : ℕ}

/--
@isnad1 id=iff.0h2v.s5.a0a22b63c638 from=translated src=- shape=a405aacb vocab=59f8af51
-/
theorem mem_verts {e : Finset (Fin n)} : e ∈ verts n ↔ e.card = 2 := by
  simp [verts, Finset.mem_powersetCard]

/-- For two edges, "equal or adjacent" means "sharing a vertex".
@isnad1 id=iff.2h3v.s5.0b56e5fb123d from=translated src=- shape=05e49e56 vocab=b8fe3aff
-/
theorem closed_iff {e f : Finset (Fin n)} (he : e.card = 2) (hf : f.card = 2) :
    (f = e ∨ Adj e f) ↔ (e ∩ f).Nonempty := by
  unfold Adj
  constructor
  · rintro (rfl | h)
    · rw [Finset.inter_self]
      exact Finset.card_pos.mp (by omega)
    · exact Finset.card_pos.mp (by omega)
  · intro h
    by_cases hfe : f = e
    · exact Or.inl hfe
    · right
      have h1 : 0 < (e ∩ f).card := Finset.card_pos.mpr h
      have h2 : (e ∩ f).card ≤ 2 := he ▸ Finset.card_le_card Finset.inter_subset_left
      by_contra h3
      have e1 : e ∩ f = e := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have e2 : e ∩ f = f := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact hfe (e2.symm.trans e1)

/--
@isnad1 id=iff.0h3v.s6.e3f6a950b054 from=translated src=- shape=8a371e47 vocab=ae9bf85f
-/
theorem deg_eq_zero {S : Finset (Finset (Fin n))} {w : Fin n} :
    deg S w = 0 ↔ ∀ g ∈ S, w ∉ g := by
  simp [deg, Finset.filter_eq_empty_iff]

/--
@isnad1 id=iff.0h3v.s6.303619781a14 from=translated src=- shape=2135564b vocab=ae9bf85f
-/
theorem deg_eq_one {S : Finset (Finset (Fin n))} {x : Fin n} :
    deg S x = 1 ↔ ∃ e ∈ S, x ∈ e ∧ ∀ g ∈ S, x ∈ g → g = e := by
  unfold deg
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨e, he⟩
    have h1 : e ∈ S.filter (fun e => x ∈ e) := by
      rw [he]
      exact Finset.mem_singleton_self e
    rw [Finset.mem_filter] at h1
    refine ⟨e, h1.1, h1.2, fun g hg hx => ?_⟩
    have h2 : g ∈ S.filter (fun e => x ∈ e) := Finset.mem_filter.mpr ⟨hg, hx⟩
    rw [he] at h2
    exact Finset.mem_singleton.mp h2
  · rintro ⟨e, heS, hxe, h⟩
    refine ⟨e, ?_⟩
    ext g
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨a, b⟩
      exact h g a b
    · rintro rfl
      exact ⟨heS, hxe⟩

/-- An edge `e ∈ S` has a private closed neighbour iff both its endpoints have degree 1, or one
of them has and some vertex is uncovered.
@isnad1 id=iff.2h3v.s7.111610f6cae5 from=translated src=- shape=830508a2 vocab=92c40e91
-/
theorem priv_iff {S : Finset (Finset (Fin n))} (hS : S ⊆ verts n) {e : Finset (Fin n)}
    (he : e ∈ S) :
    (∃ f ∈ verts n, (f = e ∨ Adj e f) ∧ ∀ g ∈ S, g ≠ e → ¬ (f = g ∨ Adj g f)) ↔
      (∀ x ∈ e, deg S x = 1) ∨ ((∃ x ∈ e, deg S x = 1) ∧ Unc S) := by
  have hc : ∀ g ∈ S, g.card = 2 := fun g hg => mem_verts.mp (hS hg)
  constructor
  · rintro ⟨f, hf, hef, hg⟩
    have hf2 := mem_verts.mp hf
    rw [closed_iff (hc e he) hf2] at hef
    have hg' : ∀ g ∈ S, g ≠ e → ∀ y ∈ f, y ∉ g := by
      intro g hgS hne y hyf hyg
      exact hg g hgS hne
        ((closed_iff (hc g hgS) hf2).mpr ⟨y, Finset.mem_inter.mpr ⟨hyg, hyf⟩⟩)
    obtain ⟨x, hx⟩ := hef
    rw [Finset.mem_inter] at hx
    have hdx : ∀ y ∈ f, y ∈ e → deg S y = 1 := fun y hyf hye =>
      deg_eq_one.mpr ⟨e, he, hye, fun g hgS hyg => by
        by_contra hne
        exact hg' g hgS hne y hyf hyg⟩
    by_cases hfe : f ⊆ e
    · have hfe' : f = e := Finset.eq_of_subset_of_card_le hfe (by rw [hc e he, hf2])
      exact Or.inl fun y hy => hdx y (hfe' ▸ hy) hy
    · obtain ⟨w, hwf, hwe⟩ := Finset.not_subset.mp hfe
      refine Or.inr ⟨⟨x, hx.1, hdx x hx.2 hx.1⟩, w, deg_eq_zero.mpr fun g hgS hwg => ?_⟩
      by_cases hne : g = e
      · exact hwe (hne ▸ hwg)
      · exact hg' g hgS hne w hwf hwg
  · rintro (h | ⟨⟨x, hxe, hx⟩, w, hw⟩)
    · refine ⟨e, hS he, Or.inl rfl, fun g hgS hne hcl => ?_⟩
      rw [closed_iff (hc g hgS) (hc e he)] at hcl
      obtain ⟨y, hy⟩ := hcl
      rw [Finset.mem_inter] at hy
      obtain ⟨e', -, -, huniq⟩ := deg_eq_one.mp (h y hy.2)
      exact hne ((huniq g hgS hy.1).trans (huniq e he hy.2).symm)
    · rw [deg_eq_zero] at hw
      obtain ⟨e', -, -, huniq⟩ := deg_eq_one.mp hx
      have hxw : x ≠ w := fun h => hw e he (h ▸ hxe)
      have hf2 : ({x, w} : Finset (Fin n)).card = 2 := Finset.card_pair hxw
      refine ⟨{x, w}, mem_verts.mpr hf2,
        (closed_iff (hc e he) hf2).mpr ⟨x, by simp [hxe]⟩, fun g hgS hne hcl => ?_⟩
      rw [closed_iff (hc g hgS) hf2] at hcl
      obtain ⟨y, hy⟩ := hcl
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hy
      obtain ⟨hyg, rfl | rfl⟩ := hy
      · exact hne ((huniq g hgS hyg).trans (huniq e he hxe).symm)
      · exact hw g hgS hyg

end A347722.Char

namespace A347722

/-- A set `S` of vertices of the triangular graph `T(n)` (edges of `K_n`) is irredundant iff it
is a star forest with an uncovered vertex, or a perfect matching.
@isnad1 id=iff.1h2v.s5.8c2f883581db from=translated src=- shape=f6f6c551 vocab=e1ae05aa
-/
theorem irredundant_iff {n : ℕ} (S : Finset (Finset (Fin n))) (hS : S ⊆ verts n) :
    Irredundant S ↔ (Star S ∧ Unc S) ∨ PM S := by
  have key : Irredundant S ↔
      ∀ e ∈ S, (∀ x ∈ e, deg S x = 1) ∨ ((∃ x ∈ e, deg S x = 1) ∧ Unc S) := by
    unfold Irredundant
    exact forall₂_congr fun e he => Char.priv_iff hS he
  rw [key]
  by_cases hU : Unc S
  · constructor
    · intro h
      refine Or.inl ⟨fun e he => ?_, hU⟩
      rcases h e he with h1 | h1
      · have hpos : 0 < e.card := by
          rw [Char.mem_verts.mp (hS he)]
          norm_num
        obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
        exact ⟨x, hx, h1 x hx⟩
      · exact h1.1
    · rintro (⟨hs, -⟩ | hp)
      · exact fun e he => Or.inr ⟨hs e he, hU⟩
      · obtain ⟨v, hv⟩ := hU
        have := hp v
        omega
  · constructor
    · intro h
      refine Or.inr fun v => ?_
      have hv : ¬ ∀ g ∈ S, v ∉ g := fun h0 => hU ⟨v, Char.deg_eq_zero.mpr h0⟩
      push Not at hv
      obtain ⟨g, hg, hvg⟩ := hv
      rcases h g hg with h1 | h1
      · exact h1 v hvg
      · exact absurd h1.2 hU
    · rintro (⟨-, hu⟩ | hp)
      · exact absurd hu hU
      · exact fun e he => Or.inl fun x _ => hp x

end A347722

