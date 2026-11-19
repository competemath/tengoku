import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.TorsoPathTrim
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.RootedIndexed
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.RegionLinkage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Path and linkage transport for gluing a rooted far side through a torso. -/

namespace HadwigerLean
namespace Linkedness

/-- A path in an induced graph maps to an ambient path with exactly the image support.
@isnad1 id=ex.0h6v.s7.094234ee2af1 from=translated src=- shape=32417adc vocab=03ceaa80
-/
theorem path_lift_induce_support
    {V : Type*} (G : SimpleGraph V) (S : Set V)
    {s t : S} (p : (G.induce S).Path s t) :
    ∃ q : G.Path (s : V) (t : V),
      pathVertexSet q = Subtype.val '' pathVertexSet p := by
  let e : (G.induce S).Embedding G := SimpleGraph.Embedding.induce S
  let q : G.Path (s : V) (t : V) := p.mapEmbedding e
  refine ⟨q, ?_⟩
  ext x
  change x ∈ ((p : (G.induce S).Walk s t).map e.toHom).support ↔
    x ∈ Subtype.val '' pathVertexSet p
  rw [SimpleGraph.Walk.support_map]
  simp only [List.mem_map]
  constructor
  · rintro ⟨u,hu,hux⟩
    exact ⟨u,hu,hux⟩
  · rintro ⟨u,hu,hux⟩
    exact ⟨u,hu,hux⟩

/-- The ambient image of an induced path support is connected.
@isnad1 id=connecte.0h6v.s6.844e3744bcd0 from=translated src=- shape=2aed9904 vocab=71002cd4
-/
theorem connected_induce_path_image
    {V : Type*} (G : SimpleGraph V) (S : Set V)
    {s t : S} (p : (G.induce S).Path s t) :
    (G.induce (Subtype.val '' pathVertexSet p)).Connected := by
  obtain ⟨q,hq⟩ := path_lift_induce_support G S p
  rw [← hq]
  exact (q : G.Walk (s : V) (t : V)).connected_induce_support

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A torso path visits the completed adhesion.-/
def TorsoPathHit (G : SimpleGraph V) (S : VertexSeparation G)
    {s t : S.left} (p : (torsoGraph G S).Path s t) : Prop :=
  ∃ x, x ∈ pathVertexSet p ∧ (x : V) ∈ S.right

/-- The chosen outer path pieces at the first and last adhesion visits.-/
noncomputable def torsoPathEndsChosen (G : SimpleGraph V)
    (S : VertexSeparation G) {s t : S.left}
    (p : (torsoGraph G S).Path s t) (h : TorsoPathHit G S p) :
    TorsoPathEnds G S p :=
  Classical.choice (TorsoPathEnds.exists_of_boundary_hit G S p h)

/-- Pair the first and last adhesion visits of every torso path that meets it.-/
noncomputable def torsoCrossingPairs (G : SimpleGraph V)
    (S : VertexSeparation G)
    {ι : Type*} {P : IndexedPairs ι S.left}
    (L : IndexedLinkage (torsoGraph G S) P) :
    IndexedPairs {i : ι // TorsoPathHit G S (L.path i)} S.right where
  start i :=
    ⟨((torsoPathEndsChosen G S (L.path i.val) i.property).first : V),
      (torsoPathEndsChosen G S (L.path i.val) i.property).first_mem⟩
  finish i :=
    ⟨((torsoPathEndsChosen G S (L.path i.val) i.property).last : V),
      (torsoPathEndsChosen G S (L.path i.val) i.property).last_mem⟩

/-- Different torso paths give disjoint adhesion endpoint pairs.
@isnad1 id=disjoint.0h6v.s6.ee97c3bf3b36 from=translated src=- shape=60e090f6 vocab=3e3d3f46
-/
theorem torsoCrossingPairs_disjoint (G : SimpleGraph V)
    (S : VertexSeparation G)
    {ι : Type*} {P : IndexedPairs ι S.left}
    (L : IndexedLinkage (torsoGraph G S) P) :
    (torsoCrossingPairs G S L).DisjointTerminals := by
  let Q := torsoCrossingPairs G S L
  have hendpoint (i : {i : ι // TorsoPathHit G S (L.path i)})
      (u : S.right) (hu : u ∈ Q.terminals i) :
      ∃ w : S.left, w ∈ pathVertexSet (L.path i.val) ∧ (w : V) = u := by
    let E := torsoPathEndsChosen G S (L.path i.val) i.property
    change u = Q.start i ∨ u = Q.finish i at hu
    rcases hu with rfl | rfl
    · exact ⟨E.first, E.first_mem_path G S, rfl⟩
    · exact ⟨E.last, E.last_mem_path G S, rfl⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hui huj
  obtain ⟨a,ha,hau⟩ := hendpoint i u hui
  obtain ⟨b,hb,hbu⟩ := hendpoint j u huj
  have hab : a = b := Subtype.val_injective (hau.trans hbu.symm)
  exact (Set.disjoint_left.mp (L.disjoint
    (fun heq => hij (Subtype.ext heq)))) ha (hab ▸ hb)

/-- Every crossing-pair endpoint belongs to the original separation adhesion.
@isnad1 id=le.0h7v.s7.62b0060faab8 from=translated src=- shape=c07be352 vocab=5eb39051
-/
theorem torsoCrossingPairs_terminals_subset (G : SimpleGraph V)
    (S : VertexSeparation G)
    {ι : Type*} {P : IndexedPairs ι S.left}
    (L : IndexedLinkage (torsoGraph G S) P)
    (i : {i : ι // TorsoPathHit G S (L.path i)}) :
    (torsoCrossingPairs G S L).terminals i ⊆
      (separationBoundaryFinset S : Set S.right) := by
  let Q := torsoCrossingPairs G S L
  intro u hu
  change u = Q.start i ∨ u = Q.finish i at hu
  rcases hu with rfl | rfl
  · exact (mem_separationBoundaryFinset S _).mpr
      (torsoPathEndsChosen G S (L.path i.val) i.property).first.property
  · exact (mem_separationBoundaryFinset S _).mpr
      (torsoPathEndsChosen G S (L.path i.val) i.property).last.property

/-- Far-side rooted linkedness joins all first-to-last adhesion pairs.
@isnad1 id=ex.1h6v.s8.03346067fa2f from=translated src=- shape=3894bf30 vocab=32711e35
-/
theorem exists_torso_crossing_linkage (G : SimpleGraph V)
    (S : VertexSeparation G)
    {ι : Type*} [Fintype ι]
    {P : IndexedPairs ι S.left}
    (L : IndexedLinkage (torsoGraph G S) P)
    (hfar : RootedLinked (G.induce S.right) (separationBoundaryFinset S)) :
    ∃ B : IndexedLinkage (G.induce S.right) (torsoCrossingPairs G S L),
      InteriorsAvoid B (separationBoundaryFinset S) := by
  classical
  letI : Fintype S.right := Fintype.ofFinite S.right
  exact hfar.linkage_finite_allow_equal (separationBoundaryFinset S)
    (torsoCrossingPairs G S L)
    (torsoCrossingPairs_disjoint G S L)
    (torsoCrossingPairs_terminals_subset G S L)
/-- Choose the unchanged near-side path when no adhesion vertex is visited.-/
noncomputable def torsoNoHitPath (G : SimpleGraph V)
    (S : VertexSeparation G) {s t : S.left}
    (p : (torsoGraph G S).Path s t)
    (hno : ¬ TorsoPathHit G S p) :
    (G.induce S.left).Path s t :=
  Classical.choose (torso_path_transfer_of_no_boundary G S p hno)

/--
@isnad1 id=eq.1h6v.s6.4e4a6dd3d0d4 from=translated src=- shape=0108c07b vocab=5bca0aa6
-/
theorem torsoNoHitPath_support (G : SimpleGraph V)
    (S : VertexSeparation G) {s t : S.left}
    (p : (torsoGraph G S).Path s t)
    (hno : ¬ TorsoPathHit G S p) :
    pathVertexSet (torsoNoHitPath G S p hno) = pathVertexSet p :=
  Classical.choose_spec (torso_path_transfer_of_no_boundary G S p hno)

/-- A far-side linkage path can meet the near side only at its own selected
adhesion endpoints; both lie on its original torso path.
@isnad1 id=ex.3h9v.s9.9343fba8939b from=translated src=- shape=f9acd73d vocab=b621f4b8
-/
theorem crossing_path_near_overlap
    (G : SimpleGraph V) (S : VertexSeparation G)
    {ι : Type*} {P : IndexedPairs ι S.left}
    (L : IndexedLinkage (torsoGraph G S) P)
    (B : IndexedLinkage (G.induce S.right) (torsoCrossingPairs G S L))
    (hB : InteriorsAvoid B (separationBoundaryFinset S))
    (i : {i : ι // TorsoPathHit G S (L.path i)})
    (x : V)
    (hxB : x ∈ Subtype.val '' pathVertexSet (B.path i))
    (hxNear : x ∈ S.left) :
    ∃ w : S.left, w ∈ pathVertexSet (L.path i.val) ∧ (w : V) = x := by
  let Q := torsoCrossingPairs G S L
  obtain ⟨u,hu,hux⟩ := hxB
  have huZ : u ∈ separationBoundaryFinset S :=
    (mem_separationBoundaryFinset S u).mpr (hux ▸ hxNear)
  have huTerm : u ∈ Q.terminals i := hB i u hu huZ
  change u = Q.start i ∨ u = Q.finish i at huTerm
  let E := torsoPathEndsChosen G S (L.path i.val) i.property
  rcases huTerm with hfirst | hlast
  · exact ⟨E.first, E.first_mem_path G S,
      by exact (congrArg Subtype.val hfirst.symm).trans hux⟩
  · exact ⟨E.last, E.last_mem_path G S,
      by exact (congrArg Subtype.val hlast.symm).trans hux⟩
end Linkedness
end HadwigerLean
