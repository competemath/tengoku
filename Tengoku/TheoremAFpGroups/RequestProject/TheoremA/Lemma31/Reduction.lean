module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Lemma31.ConeComplex
public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lemma 3.1 from developability of cone complexes of groups

Following the proof of Lemma 3.1 in the manuscript, `K_Σ(G)` is compared with the colimit of the
cone complex of groups with local groups `G` at the indices and `G × G` at the triples, the maps
into the local group of `ℓ = (i, j) ⟶ k` being `g ↦ (g, 1)`, `g ↦ (1, g)`, `g ↦ (g, g)` (eq. (3.2)).

* `TheoremA.tripleComplex` is this cone complex of groups;
* `TheoremA.tripleComplex_npc`: it is non-positively curved as soon as `girth(L) ≥ 12` (the three
  subgroups `G × 1`, `1 × G`, `diag G` of `G × G` pairwise intersect trivially, even for
  non-abelian `G`);
* `TheoremA.lemma31_of_coneDevelopable`: Lemma 3.1 follows from `ConeDevelopable`.
-/

@[expose] public section

namespace TheoremA

open TripleSystem

universe u

/-- The structure map `G → G × G` attached to an index `v` of a triple `t` (eq. (3.2)).-/
def tripleMap (G : Type u) [Group G] (t : Triple) (v : ℕ) : G →* G × G :=
  if v = t.1 then MonoidHom.inl G G
  else if v = t.2.1 then MonoidHom.inr G G
  else MonoidHom.prod (MonoidHom.id G) (MonoidHom.id G)

/-- The cone complex of groups of the proof of Lemma 3.1.-/
def tripleComplex (r : ℕ) (T : List Triple) (G : Type u) [Group G] :
    ConeComplex.{u, 0} (Fin r) (Fin T.length) where
  inc v l := (v : ℕ) ∈ T[l].entries
  A _ := G
  B _ := G × G
  φ v l _ := tripleMap G T[l] v

/--
@isnad1 id=eq.0h3v.s5.5a577e2fe278 from=translated src=- shape=30a50e95 vocab=188ae26d
-/
theorem tripleComplex_graph (r : ℕ) (T : List Triple) (G : Type u) [Group G] :
    (tripleComplex r T G).graph = incidenceGraph r T := by
  ext x y
  cases x <;> cases y <;> rfl

/--
@isnad1 id=eq.5h6v.s8.8195e3986699 from=translated src=- shape=75f9698f vocab=879e8723
-/
theorem tripleMap_inter_trivial (G : Type u) [Group G] (t : Triple)
    (hd : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) (v v' : ℕ)
    (hv : v ∈ t.entries) (hv' : v' ∈ t.entries) (hne : v ≠ v') (a a' : G)
    (h : tripleMap G t v a = tripleMap G t v' a') : a = 1 := by
  simp only [Triple.entries, List.mem_cons, List.not_mem_nil, or_false] at hv hv'
  obtain ⟨h12, h13, h23⟩ := hd
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h32 := Ne.symm h23
  rcases hv with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;>
    simp_all [tripleMap, Prod.ext_iff]
  grind

/--
@isnad1 id=npc.2h3v.s5.814eb69347c9 from=translated src=- shape=7b6e27dd vocab=3a13e5da
-/
theorem tripleComplex_npc (r : ℕ) (T : List Triple) (hw : WellFormed r T)
    (hg : 12 ≤ (incidenceGraph r T).egirth) (G : Type u) [Group G] :
    (tripleComplex r T G).NPC where
  φ_injective v l _ := by
    intro a b hab
    change tripleMap G T[l] v a = tripleMap G T[l] v b at hab
    unfold tripleMap at hab
    split_ifs at hab <;> simp_all [Prod.ext_iff]
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)
  inter_trivial v v' l h h' hne a a' e := by
    have hd := hw T[l] (List.getElem_mem _)
    exact tripleMap_inter_trivial G T[l] ⟨hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩ v v' h h'
      (fun hvv => hne (Fin.ext hvv)) a a' e
  girth := by rw [tripleComplex_graph]; exact hg

end TheoremA
