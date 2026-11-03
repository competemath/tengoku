module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Lemma31.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `K_Σ(G)` is isomorphic to the colimit of the cone complex of groups

`TheoremA.toColim` (in `Reduction.lean`) is the map `K_Σ(G) → colim` sending `g_v` to the image of
`g` in the local group at `v`.  Here we construct the inverse map `colim → K_Σ(G)`: at the index
`v` it is `ι_v`, and at a triple `ℓ = (i, j) ⟶ k` it is `(g, h) ↦ g_i h_j`, which is a homomorphism
because `G_i` and `G_j` commute in `K_Σ(G)`; it is compatible with the structure maps
`(g,1), (1,g), (g,g)` because `g_k = g_i g_j` in `K_Σ(G)`.

* `TheoremA.fromColim` — the map `colim → K_Σ(G)`;
* `TheoremA.diagramGroupEquivColim` — `K_Σ(G) ≃* colim`, whose forward map is `toColim`.
-/

@[expose] public section

namespace TheoremA

open TripleSystem

universe u

variable (r : ℕ) (T : List Triple) (hw : WellFormed r T) (G : Type u) [Group G]

/--
@isnad1 id=eq.1h4v.s11.053533a71c5c from=translated src=- shape=764be901 vocab=c53259df
-/
theorem diagramGroup.ι_eq_one_of_mem {x : Monoid.CoprodI fun _ : Fin r => G}
    (hx : x ∈ relators r T G) :
    (QuotientGroup.mk' (Subgroup.normalClosure (relators r T G)) x : diagramGroup r T G) = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure hx

/-- In `K_Σ(G)`, the copies `G_i` and `G_j` of a triple `(i, j) ⟶ k` commute.
@isnad1 id=commute.4h6v.s9.2d7152ab5225 from=translated src=- shape=e0160d41 vocab=cfc551ba
-/
theorem diagramGroup.commute_ι (t : Triple) (ht : t ∈ T) (hi : t.1 < r) (hj : t.2.1 < r)
    (hk : t.2.2 < r) (g h : G) :
    Commute (diagramGroup.ι r T G ⟨t.1, hi⟩ g) (diagramGroup.ι r T G ⟨t.2.1, hj⟩ h) := by
  have := diagramGroup.ι_eq_one_of_mem r T G ⟨t, ht, hi, hj, hk, Or.inl ⟨g, h, rfl⟩⟩
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at this
  exact this

/-- In `K_Σ(G)`, `g_k = g_i g_j` for a triple `(i, j) ⟶ k`.
@isnad1 id=eq.4h5v.s9.1500502136e6 from=translated src=- shape=4ce9f7dd vocab=514d75cb
-/
theorem diagramGroup.ι_third (t : Triple) (ht : t ∈ T) (hi : t.1 < r) (hj : t.2.1 < r)
    (hk : t.2.2 < r) (g : G) :
    diagramGroup.ι r T G ⟨t.2.2, hk⟩ g =
      diagramGroup.ι r T G ⟨t.1, hi⟩ g * diagramGroup.ι r T G ⟨t.2.1, hj⟩ g := by
  have := diagramGroup.ι_eq_one_of_mem r T G ⟨t, ht, hi, hj, hk, Or.inr ⟨g, rfl⟩⟩
  simp only [map_mul, map_inv] at this
  rw [mul_assoc, inv_mul_eq_one] at this
  exact this

/-- The homomorphism `G × G → K_Σ(G)`, `(g, h) ↦ g_i h_j`, at the triple `ℓ = (i, j) ⟶ k`.-/
def tripleToK (l : Fin T.length) : G × G →* diagramGroup r T G :=
  MonoidHom.noncommCoprod
    (diagramGroup.ι r T G ⟨T[l].1, (hw T[l] (List.getElem_mem _)).1⟩)
    (diagramGroup.ι r T G ⟨T[l].2.1, (hw T[l] (List.getElem_mem _)).2.1⟩)
    (diagramGroup.commute_ι r T G T[l] (List.getElem_mem _) _ _
      (hw T[l] (List.getElem_mem _)).2.2.1)

/-- The local homomorphisms into `K_Σ(G)`.-/
def colimFamily : ∀ x, (tripleComplex r T G).loc x →* diagramGroup r T G
  | .inl v => diagramGroup.ι r T G v
  | .inr l => tripleToK r T hw G l

/--
@isnad1 id=eq.3h6v.s9.7a1e6858ddcd from=translated src=- shape=56d1f9e8 vocab=ff5405d8
-/
theorem tripleToK_tripleMap (l : Fin T.length) (v : ℕ) (hvr : v < r) (hv : v ∈ T[l].entries)
    (a : G) : diagramGroup.ι r T G ⟨v, hvr⟩ a = tripleToK r T hw G l (tripleMap G T[l] v a) := by
  have hmem := List.getElem_mem (l := T) l.isLt
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := hw T[l] (List.getElem_mem _)
  have third := diagramGroup.ι_third r T G T[l] hmem h1 h2 h3 a
  simp only [Triple.entries, List.mem_cons, List.not_mem_nil, or_false] at hv
  simp only [tripleToK, MonoidHom.noncommCoprod_apply]
  simp only [Fin.getElem_fin] at *
  rcases hv with h | h | h
  · rw [show (⟨v, hvr⟩ : Fin r) = ⟨_, h1⟩ from Fin.ext h, h]
    simp [tripleMap]
  · rw [show (⟨v, hvr⟩ : Fin r) = ⟨_, h2⟩ from Fin.ext h, h]
    simp [tripleMap, Ne.symm h12]
  · rw [show (⟨v, hvr⟩ : Fin r) = ⟨_, h3⟩ from Fin.ext h, h]
    simp [tripleMap, Ne.symm h13, Ne.symm h23]
    exact third

end TheoremA
