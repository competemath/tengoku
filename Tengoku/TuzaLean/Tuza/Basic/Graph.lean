import Tengoku.TuzaLean.Tuza.Basic.Geometry
import Tengoku.TuzaLean.Tuza.Basic.Packing
import Tengoku.Seed.Combinatorics.SimpleGraph.Clique

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The connection between finite edge families and ordinary finite simple graphs. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All actual triangles whose edges belong to the given edge set.-/
noncomputable def trianglesOn (A : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) := by
  classical
  exact univ.filter (fun T => IsTriangle T ∧ T ⊆ A)

/--
@isnad1 id=iff.0h3v.s6.3e40ff47afaa from=translated src=- shape=0ef6b343 vocab=a85d789d
-/
@[simp] theorem mem_trianglesOn {A T : Finset (Sym2 V)} :
    T ∈ trianglesOn A ↔ IsTriangle T ∧ T ⊆ A := by
  classical
  simp [trianglesOn]

/--
@isnad1 id=eq.1h3v.s5.20e4f9976994 from=translated src=- shape=6cc8ebbe vocab=021f4793
-/
theorem trianglesOn_card {A T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    T.card = 3 := (mem_trianglesOn.mp hT).1.card_eq_three

/--
@isnad1 id=nonempty.1h3v.s5.92079cb9866f from=translated src=- shape=1ff4c175 vocab=8a8f9e28
-/
theorem trianglesOn_nonempty {A T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    T.Nonempty := card_pos.mp (by rw [trianglesOn_card hT]; decide)

/--
@isnad1 id=le.1h3v.s5.9cabc0a8f80d from=translated src=- shape=abe50ab4 vocab=d6479959
-/
theorem trianglesOn_mono {A B : Finset (Sym2 V)} (h : A ⊆ B) :
    trianglesOn A ⊆ trianglesOn B := by
  intro T hT
  obtain ⟨ht, hta⟩ := mem_trianglesOn.mp hT
  exact mem_trianglesOn.mpr ⟨ht, hta.trans h⟩

/-- Edge deletion removes precisely the triangles meeting a deleted edge.
@isnad1 id=eq.0h3v.s6.5001103ecf65 from=translated src=- shape=2a7938bc vocab=0038a970
-/
theorem trianglesOn_sdiff (A C : Finset (Sym2 V)) :
    trianglesOn (A \ C) = residual (trianglesOn A) C := by
  ext T
  simp only [mem_trianglesOn, mem_residual]
  constructor
  · rintro ⟨hT, hsub⟩
    refine ⟨⟨hT, fun e he => (mem_sdiff.mp (hsub he)).1⟩, disjoint_left.mpr ?_⟩
    intro e heT heC
    exact (mem_sdiff.mp (hsub heT)).2 heC
  · rintro ⟨⟨hT, hsub⟩, hd⟩
    refine ⟨hT, fun e he => mem_sdiff.mpr ⟨hsub he, ?_⟩⟩
    exact fun heC => disjoint_left.mp hd he heC

/-- The edge set of a finite simple graph.-/
noncomputable def graphEdges (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact G.edgeSet.toFinset

omit [DecidableEq V] in
/--
@isnad1 id=iff.0h3v.s5.6998010d456d from=translated src=- shape=b4cbe4e2 vocab=2a28b7eb
-/
@[simp] theorem mem_graphEdges {G : SimpleGraph V} {e : Sym2 V} :
    e ∈ graphEdges G ↔ e ∈ G.edgeSet := by
  classical
  simp [graphEdges]

omit [DecidableEq V] in
/--
@isnad1 id=iff.0h4v.s5.61c604314a86 from=translated src=- shape=b19f8003 vocab=64350172
-/
@[simp] theorem pair_mem_graphEdges {G : SimpleGraph V} {u v : V} :
    s(u, v) ∈ graphEdges G ↔ G.Adj u v := by
  simp

/-- The family used to define the graph's packing and transversal numbers.-/
noncomputable def graphTriangles (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  trianglesOn (graphEdges G)

/-- Membership means exactly three pairwise adjacent vertices and their three edges.
@isnad1 id=iff.0h3v.s6.4fe6fe73ff42 from=translated src=- shape=e235d871 vocab=3d4a8689
-/
theorem mem_graphTriangles_iff {G : SimpleGraph V} {T : Finset (Sym2 V)} :
    T ∈ graphTriangles G ↔
      ∃ u v w, G.Adj u v ∧ G.Adj u w ∧ G.Adj v w ∧ T = triangleEdges u v w := by
  constructor
  · intro hT
    obtain ⟨⟨u, v, w, huv, huw, hvw, rfl⟩, hsub⟩ := mem_trianglesOn.mp hT
    refine ⟨u, v, w, ?_, ?_, ?_, rfl⟩
    all_goals apply pair_mem_graphEdges.mp; apply hsub; simp
  · rintro ⟨u, v, w, huv, huw, hvw, rfl⟩
    apply mem_trianglesOn.mpr
    refine ⟨isTriangle_triangleEdges huv.ne huw.ne hvw.ne, ?_⟩
    intro e he
    rcases mem_triangleEdges.mp he with rfl | rfl | rfl
    · exact pair_mem_graphEdges.mpr huv
    · exact pair_mem_graphEdges.mpr huw
    · exact pair_mem_graphEdges.mpr hvw

/-- The representation agrees with mathlib's standard three-vertex clique predicate.
@isnad1 id=iff.0h5v.s6.62cfe8c9790b from=translated src=- shape=ded0adb4 vocab=f5e96446
-/
theorem triangleEdges_mem_graphTriangles_iff {G : SimpleGraph V} {u v w : V} :
    triangleEdges u v w ∈ graphTriangles G ↔ G.IsNClique 3 {u, v, w} := by
  rw [SimpleGraph.is3Clique_triple_iff]
  constructor
  · intro h
    have hsub := (mem_trianglesOn.mp h).2
    exact ⟨pair_mem_graphEdges.mp (hsub (by simp)),
      pair_mem_graphEdges.mp (hsub (by simp)),
      pair_mem_graphEdges.mp (hsub (by simp))⟩
  · rintro ⟨hab, hac, hbc⟩
    exact mem_graphTriangles_iff.mpr ⟨u, v, w, hab, hac, hbc, rfl⟩

/-- The paper's ν(G).-/
noncomputable def nu (G : SimpleGraph V) : ℕ := packingNumber (graphTriangles G)

/-- The paper's τ(G).-/
noncomputable def tau (G : SimpleGraph V) : ℕ := transversalNumber (graphTriangles G)

/--
@isnad1 id=le.0h2v.s5.75fd2d784027 from=translated src=- shape=0e1bc939 vocab=74e61bb3
-/
theorem graph_trivial_bound (G : SimpleGraph V) : tau G ≤ 3 * nu G :=
  transversalNumber_le_three_packingNumber _ (fun _ hT => trianglesOn_card hT)

/-- The finite-family cover condition is exactly the usual requirement on
every triple of pairwise adjacent vertices.
@isnad1 id=iff.0h3v.s6.245bbd0a3936 from=translated src=- shape=2b80906b vocab=04a61d46
-/
theorem graph_cover_iff_adj (G : SimpleGraph V) (C : Finset (Sym2 V)) :
    IsCover (graphTriangles G) C ↔
      ∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u, v) ∈ C ∨ s(u, w) ∈ C ∨ s(v, w) ∈ C := by
  constructor
  · intro hC u v w huv huw hvw
    obtain ⟨e, he⟩ := hC (triangleEdges u v w)
      (mem_graphTriangles_iff.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩)
    obtain ⟨heT, heC⟩ := mem_inter.mp he
    rcases mem_triangleEdges.mp heT with rfl | rfl | rfl
    · exact Or.inl heC
    · exact Or.inr (Or.inl heC)
    · exact Or.inr (Or.inr heC)
  · intro hC T hT
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := mem_graphTriangles_iff.mp hT
    rcases hC u v w huv huw hvw with he | he | he
    · exact ⟨s(u, v), mem_inter.mpr ⟨by simp, he⟩⟩
    · exact ⟨s(u, w), mem_inter.mpr ⟨by simp, he⟩⟩
    · exact ⟨s(v, w), mem_inter.mpr ⟨by simp, he⟩⟩

/--
@isnad1 id=le.0h2v.s5.1ea8a27bb826 from=translated src=- shape=0ad4085d vocab=e7509916
-/
theorem graphTriangles_support_subset (G : SimpleGraph V) :
    support (graphTriangles G) ⊆ graphEdges G := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp hT).2 heT

/-- A minimum cover can be chosen from the graph's edges.
@isnad1 id=ex.0h2v.s6.16ce3e62477e from=translated src=- shape=3ba7e5e5 vocab=f88e6967
-/
theorem exists_graph_minimumCover (G : SimpleGraph V) :
    ∃ C, C ⊆ graphEdges G ∧ IsCover (graphTriangles G) C ∧ C.card = tau G := by
  obtain ⟨C, hsub, hC, hc⟩ := exists_minimumCover_subset_support (graphTriangles G)
    (fun _ hT => trianglesOn_nonempty hT)
  exact ⟨C, hsub.trans (graphTriangles_support_subset G), hC, hc⟩

/-- An upper bound on the formal τ is equivalent to an ordinary graph-edge
transversal of that size.
@isnad1 id=iff.0h3v.s6.6353dac41775 from=translated src=- shape=1bfe324d vocab=f88e6967
-/
theorem tau_le_iff (G : SimpleGraph V) (n : ℕ) :
    tau G ≤ n ↔ ∃ C, C ⊆ graphEdges G ∧
      IsCover (graphTriangles G) C ∧ C.card ≤ n := by
  constructor
  · intro h
    obtain ⟨C, hsub, hC, hc⟩ := exists_graph_minimumCover G
    exact ⟨C, hsub, hC, hc ▸ h⟩
  · rintro ⟨C, _, hC, hc⟩
    exact hC.number_le.trans hc

/-- The formal ν is the maximum size over actual edge-disjoint graph triangles.
@isnad1 id=iff.0h3v.s5.40bf01c8bcf5 from=translated src=- shape=793e451c vocab=3aced20e
-/
theorem le_nu_iff (G : SimpleGraph V) (n : ℕ) :
    n ≤ nu G ↔ ∃ P, IsPacking (graphTriangles G) P ∧ n ≤ P.card := by
  constructor
  · intro h
    exact ⟨maximumPacking (graphTriangles G), (maximumPacking_spec _).1, h⟩
  · rintro ⟨P, hP, hc⟩
    exact hc.trans hP.card_le

end Tuza
