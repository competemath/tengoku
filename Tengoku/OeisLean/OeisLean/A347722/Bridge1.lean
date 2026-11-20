/-
OEIS A347722, bridge part 1: the edge set of an idempotent map.

`edgeSet g` is a set of vertices of `T(n)`, it is a star forest when `g` is idempotent, its
uncovered vertices are the isolated fixed points of `g`, and `edgeSet` is injective on good maps.
-/
import Tengoku.OeisLean.OeisLean.A347722.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A347722.edgeSet_subset` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms A347722.star_edgeSet` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms A347722.unc_edgeSet_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms A347722.edgeSet_injective` (it only prints; the queue checks the axioms of every declaration). -/

namespace A347722.Bridge1

variable {n : ℕ}

/--
@isnad1 id=iff.0h3v.s6.992b9407d776 from=translated src=- shape=48bfc5a3 vocab=4b177410
-/
theorem mem_edgeSet (g : Fin n → Fin n) (e : Finset (Fin n)) :
    e ∈ edgeSet g ↔ ∃ v, g v ≠ v ∧ {v, g v} = e := by
  simp only [edgeSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A non-fixed point and its image form an edge.
@isnad1 id=mem.2h4v.s6.77ce10d069bb from=translated src=- shape=b7dc0f58 vocab=4b177410
-/
theorem pair_mem (g : Fin n → Fin n) (a b : Fin n) (h : g a = b) (hab : a ≠ b) :
    ({a, b} : Finset (Fin n)) ∈ edgeSet g :=
  (mem_edgeSet g _).2 ⟨a, by rw [h]; exact hab.symm, by rw [h]⟩

/-- An edge `{a, b}` comes from `a ↦ b` or from `b ↦ a`.
@isnad1 id=or.1h4v.s6.9509d0f9417e from=translated src=- shape=f13145ea vocab=4b177410
-/
theorem of_pair_mem (g : Fin n → Fin n) (a b : Fin n)
    (h : ({a, b} : Finset (Fin n)) ∈ edgeSet g) : g a = b ∨ g b = a := by
  obtain ⟨x, hx, he⟩ := (mem_edgeSet g _).1 h
  have h1 : x = a ∨ x = b := by
    have hm : x ∈ ({x, g x} : Finset (Fin n)) := Finset.mem_insert_self _ _
    rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm
  have h2 : g x = a ∨ g x = b := by
    have hm : g x ∈ ({x, g x} : Finset (Fin n)) := by
      rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr rfl
    rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm
  rcases h1 with rfl | rfl
  · rcases h2 with h2 | h2
    · exact absurd h2 hx
    · exact Or.inl h2
  · rcases h2 with h2 | h2
    · exact Or.inr h2
    · exact absurd h2 hx

/-- A non-fixed point of an idempotent map has degree 1.
@isnad1 id=eq.2h3v.s5.f62522f1fbed from=translated src=- shape=2488d616 vocab=68b6118e
-/
theorem deg_of_ne (g : Fin n → Fin n) (hg : Idem g) (v : Fin n) (hv : g v ≠ v) :
    deg (edgeSet g) v = 1 := by
  unfold deg
  rw [Finset.card_eq_one]
  refine ⟨{v, g v}, ?_⟩
  ext e
  rw [Finset.mem_filter, Finset.mem_singleton, mem_edgeSet]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hve⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | h
    · rfl
    · exact absurd (by rw [h, hg w]) hv
  · rintro rfl
    exact ⟨⟨v, hv, rfl⟩, Finset.mem_insert_self _ _⟩

/-- A fixed point has degree 0 iff it has no other preimage.
@isnad1 id=iff.1h3v.s5.18ec838d7d21 from=translated src=- shape=b4ddf678 vocab=66d3bb92
-/
theorem deg_eq_zero_iff (g : Fin n → Fin n) (v : Fin n) (hv : g v = v) :
    deg (edgeSet g) v = 0 ↔ ∀ w, g w = v → w = v := by
  unfold deg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h w hw
    by_contra hne
    refine h (pair_mem g w v hw hne) ?_
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr rfl
  · intro h e he hve
    obtain ⟨w, hw, rfl⟩ := (mem_edgeSet g _).1 he
    rw [Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | h'
    · exact hw hv
    · exact hw (h'.symm.trans (h w h'.symm).symm)

/-- If `g₁ v = w ≠ v` but `g₂ w = v`, then `w` is bad for `g₁` unless `¬ v < w`.
@isnad1 id=not.6h5v.s6.b962c211ecdb from=translated src=- shape=a59805ba vocab=dca707b8
-/
theorem half (g₁ g₂ : Fin n → Fin n) (h₁ : Good g₁) (hi2 : Idem g₂)
    (h : edgeSet g₁ = edgeSet g₂) (v w : Fin n) (hvw : v ≠ w) (hw1 : g₁ v = w)
    (hw2 : g₂ w = v) : ¬ v < w := by
  intro hlt
  have hfix : g₁ w = w := by rw [← hw1]; exact h₁.1 v
  refine h₁.2 w ⟨hfix, v, hlt, hw1, fun y hy => ?_⟩
  by_cases hyw : y = w
  · exact Or.inr hyw
  · left
    have hm : ({y, w} : Finset (Fin n)) ∈ edgeSet g₂ := by
      rw [← h]; exact pair_mem g₁ y w hy hyw
    rcases of_pair_mem g₂ _ _ hm with h' | h'
    · exfalso
      have h3 : g₂ w = w := by rw [← h']; exact hi2 y
      exact hvw (hw2.symm.trans h3)
    · exact h'.symm.trans hw2

/-- The one-sided form of injectivity.
@isnad1 id=eq.4h4v.s5.7f43c2ecd83d from=translated src=- shape=1f77309f vocab=9e559adf
-/
theorem one_sided (g₁ g₂ : Fin n → Fin n) (h₁ : Good g₁) (h₂ : Good g₂)
    (h : edgeSet g₁ = edgeSet g₂) (v : Fin n) (hv : g₁ v ≠ v) : g₂ v = g₁ v := by
  have hm : ({v, g₁ v} : Finset (Fin n)) ∈ edgeSet g₂ := by
    rw [← h]; exact pair_mem g₁ v _ rfl (Ne.symm hv)
  rcases of_pair_mem g₂ _ _ hm with h' | h'
  · exact h'
  · exfalso
    rcases lt_or_gt_of_ne (Ne.symm hv) with hlt | hlt
    · exact half g₁ g₂ h₁ h₂.1 h v (g₁ v) (Ne.symm hv) rfl h' hlt
    · exact half g₂ g₁ h₂ h₁.1 h.symm (g₁ v) v hv h' rfl hlt

end A347722.Bridge1

namespace A347722

open Bridge1

/-- Every edge of `edgeSet g` is a 2-element subset, i.e. a vertex of `T(n)`.
@isnad1 id=le.0h2v.s5.f6bffbcbc916 from=translated src=- shape=078a320f vocab=c003edaf
-/
theorem edgeSet_subset {n : ℕ} (g : Fin n → Fin n) : edgeSet g ⊆ verts n := by
  intro e he
  obtain ⟨v, hv, rfl⟩ := (mem_edgeSet g _).1 he
  unfold verts
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, Finset.card_pair (Ne.symm hv)⟩

/-- The edge set of an idempotent map is a star forest: the leaf of each edge has degree 1.
@isnad1 id=star.1h2v.s4.16c7050bec65 from=translated src=- shape=5403d4af vocab=4d283870
-/
theorem star_edgeSet {n : ℕ} (g : Fin n → Fin n) (hg : Idem g) : Star (edgeSet g) := by
  intro e he
  obtain ⟨v, hv, rfl⟩ := (mem_edgeSet g _).1 he
  exact ⟨v, Finset.mem_insert_self _ _, deg_of_ne g hg v hv⟩

/-- The edge set of an idempotent map leaves a vertex uncovered iff the map has an isolated
fixed point.
@isnad1 id=iff.1h2v.s4.03349b13121e from=translated src=- shape=6ec3600a vocab=48a64a9e
-/
theorem unc_edgeSet_iff {n : ℕ} (g : Fin n → Fin n) (hg : Idem g) :
    Unc (edgeSet g) ↔ ∃ v, IsoAt g v := by
  constructor
  · rintro ⟨v, hv⟩
    have hfix : g v = v := by
      by_contra hne
      rw [deg_of_ne g hg v hne] at hv
      exact one_ne_zero hv
    exact ⟨v, fun w => ⟨(deg_eq_zero_iff g v hfix).1 hv w, fun hwv => by rw [hwv]; exact hfix⟩⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, (deg_eq_zero_iff g v ((hv v).2 rfl)).2 fun w hw => (hv w).1 hw⟩

/-- A good map is determined by its edge set.
@isnad1 id=eq.3h3v.s5.7539e73427e5 from=translated src=- shape=dc1951cf vocab=9e559adf
-/
theorem edgeSet_injective {n : ℕ} (g₁ g₂ : Fin n → Fin n) (h₁ : Good g₁) (h₂ : Good g₂)
    (h : edgeSet g₁ = edgeSet g₂) : g₁ = g₂ := by
  funext v
  by_cases ha : g₁ v = v
  · by_cases hb : g₂ v = v
    · rw [ha, hb]
    · exact absurd ((one_sided g₂ g₁ h₂ h₁ h.symm v hb).symm.trans ha) hb
  · exact (one_sided g₁ g₂ h₁ h₂ h v ha).symm

end A347722

