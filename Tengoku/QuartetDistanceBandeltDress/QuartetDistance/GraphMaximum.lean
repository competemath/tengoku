import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.GraphModel
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.GraphQuartet
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Maximum
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Upper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The conventional graph domain for quartet distance

This file packages finite graph-theoretic binary phylogenetic trees whose
vertex types may have different cardinalities.  Each vertex type is put in
the canonical form `Fin m`; this avoids existential typeclass packaging while
still representing every finite graph up to a label-preserving isomorphism.

It then proves invariance of edge separation under label-preserving graph
isomorphisms, uniqueness of the directly displayed quartet topology, equality
of graph and syntax quartet distances under both encodings, and exact equality
of their maxima for `n ≥ 4`.
-/

namespace QuartetDistance

open SimpleGraph

noncomputable local instance finiteNeighborSet
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Fintype (G.neighborSet v) :=
  Fintype.ofFinite _

/-- A conventional finite binary phylogenetic tree with a canonical finite
vertex type.  Different values of this type may have different vertex counts.-/
structure CanonicalBinaryPhyloGraph (α : Type*) [Fintype α] where
  vertexCount : ℕ
  tree : GraphModel.BinaryPhyloGraph α (Fin vertexCount)

namespace GraphModel.BinaryPhyloGraph

variable {α V : Type*} [Fintype α] [Fintype V] [DecidableEq V]

/-- The canonical graph isomorphism from a finite vertex type to `Fin` of its
cardinality.-/
noncomputable def canonicalIso (P : BinaryPhyloGraph α V) :
    P.G ≃g P.G.overFin rfl :=
  P.G.overFinIso rfl

/-- Put an independently defined finite binary phylogenetic graph on the
canonical vertex type `Fin (Fintype.card V)`.-/
noncomputable def canonicalize (P : BinaryPhyloGraph α V) :
    CanonicalBinaryPhyloGraph α where
  vertexCount := Fintype.card V
  tree :=
    { G := P.G.overFin rfl
      isTree := (P.canonicalIso.isTree_iff).mp P.isTree
      leafEquiv := P.leafEquiv.trans <|
        P.canonicalIso.toEquiv.subtypeEquiv fun v => by
          change P.G.degree v = 1 ↔
            (P.G.overFin rfl).degree (P.canonicalIso v) = 1
          rw [P.canonicalIso.degree_eq]
      internal_degree := by
        intro w hw
        obtain ⟨v, rfl⟩ := P.canonicalIso.surjective w
        rw [P.canonicalIso.degree_eq] at hw ⊢
        exact P.internal_degree v hw }

omit [DecidableEq V] in
@[simp] theorem canonicalize_vertexCount (P : BinaryPhyloGraph α V) :
    P.canonicalize.vertexCount = Fintype.card V :=
  rfl

omit [DecidableEq V] in
@[simp] theorem canonicalize_graph (P : BinaryPhyloGraph α V) :
    P.canonicalize.tree.G = P.G.overFin rfl :=
  rfl

omit [DecidableEq V] in
/-- Canonicalization preserves each labelled leaf, not merely the underlying
unlabelled graph.-/
@[simp] theorem canonicalIso_leafVertex (P : BinaryPhyloGraph α V) (a : α) :
    P.canonicalIso (P.leafVertex a) = P.canonicalize.tree.leafVertex a :=
  rfl

/-- The partial labelling carried by the degree-one vertices of a conventional
phylogenetic graph.-/
noncomputable def leafLabel? (P : BinaryPhyloGraph α V) (v : V) : Option α :=
  if hv : P.G.degree v = 1 then some (P.labelOfLeaf v hv) else none

omit [Fintype α] in
@[simp] theorem leafLabel?_leafVertex (P : BinaryPhyloGraph α V) (a : α) :
    P.leafLabel? (P.leafVertex a) = some a := by
  simp [leafLabel?, P.degree_leafVertex]

omit [Fintype α] in
theorem leafLabel?_eq_some_iff (P : BinaryPhyloGraph α V) (v : V) (a : α) :
    P.leafLabel? v = some a ↔ v = P.leafVertex a := by
  classical
  unfold leafLabel?
  split_ifs with hv
  · constructor
    · intro h
      have ha : P.labelOfLeaf v hv = a := Option.some.inj h
      rw [← ha, P.leafVertex_labelOfLeaf]
    · intro h
      subst v
      simp
  · constructor
    · intro h
      cases h
    · intro h
      subst v
      exact hv (P.degree_leafVertex a)

end GraphModel.BinaryPhyloGraph

namespace Tree.PhyloTree

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The degree-one labelling recovered from the graph realization is exactly
the original syntax labelling at every vertex.-/
theorem toBinaryPhyloGraph_leafLabel? (T : Tree.PhyloTree α)
    (v : TreeAdequacy.PhyloTree.Vertex T) :
    T.toBinaryPhyloGraph.leafLabel? v =
      TreeAdequacy.PhyloTree.label? T v := by
  apply Option.ext
  intro a
  rw [GraphModel.BinaryPhyloGraph.leafLabel?_eq_some_iff,
    T.toBinaryPhyloGraph_leafVertex]
  constructor
  · rintro rfl
    exact T.label_labelledVertex a
  · intro h
    exact T.label_unique h (T.label_labelledVertex a)

/-- The canonical conventional graph associated with a syntax tree.-/
noncomputable def toCanonicalBinaryPhyloGraph (T : Tree.PhyloTree α) :
    CanonicalBinaryPhyloGraph α :=
  T.toBinaryPhyloGraph.canonicalize

/-- The syntax realization is label-preservingly isomorphic to its canonical
`Fin`-vertex presentation.-/
noncomputable def toCanonicalGraphIso (T : Tree.PhyloTree α) :
    TreeAdequacy.PhyloTree.graph T ≃g T.toCanonicalBinaryPhyloGraph.tree.G :=
  T.toBinaryPhyloGraph.canonicalIso

end Tree.PhyloTree

namespace CanonicalBinaryPhyloGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Encode a canonical conventional graph after choosing the leaf at which
to cut it open.-/
noncomputable def encodeAt (P : CanonicalBinaryPhyloGraph α) (rootLabel : α) :
    Tree.PhyloTree α :=
  P.tree.encode rootLabel

/-- The encoding of a canonical conventional graph realizes to the original
graph on `Fin P.vertexCount`.-/
noncomputable def encodeGraphIsoAt (P : CanonicalBinaryPhyloGraph α)
    (rootLabel : α) :
    TreeAdequacy.PhyloTree.graph (P.encodeAt rootLabel) ≃g P.tree.G :=
  P.tree.encodeGraphIso rootLabel

@[simp] theorem encodeGraphIsoAt_label (P : CanonicalBinaryPhyloGraph α)
    (rootLabel a : α)
    (x : TreeAdequacy.PhyloTree.Vertex (P.encodeAt rootLabel)) :
    P.tree.leafLabel? (P.encodeGraphIsoAt rootLabel x) = some a ↔
      TreeAdequacy.PhyloTree.label? (P.encodeAt rootLabel) x = some a := by
  rw [GraphModel.BinaryPhyloGraph.leafLabel?_eq_some_iff]
  exact (P.tree.encodeGraphIso_label_iff rootLabel a x).symm

/-- The graph isomorphism from the syntax encoding preserves the entire
partial taxon labelling.-/
theorem encodeGraphIsoAt_leafLabel? (P : CanonicalBinaryPhyloGraph α)
    (rootLabel : α)
    (x : TreeAdequacy.PhyloTree.Vertex (P.encodeAt rootLabel)) :
    P.tree.leafLabel? (P.encodeGraphIsoAt rootLabel x) =
      TreeAdequacy.PhyloTree.label? (P.encodeAt rootLabel) x := by
  apply Option.ext
  intro a
  exact P.encodeGraphIsoAt_label rootLabel a x

/-- A split is displayed by a conventional graph when it is a well-formed
split of `Q` and some two distinct sides are separated by a graph edge.-/
def GraphDisplaysSplit (P : CanonicalBinaryPhyloGraph α)
    (Q : Finset α) (s : Circular.QuartetSplit α) : Prop :=
  Circular.IsQuartetSplit Q s ∧
    ∃ A ∈ s, ∃ B ∈ s, A ≠ B ∧
      GraphQuartet.EdgeSeparates P.tree.G P.tree.leafLabel? A B

/-- Direct graph-theoretic display of one of the three channels on a labelled
quartet.-/
def GraphDisplaysTopology (P : CanonicalBinaryPhyloGraph (Fin n))
    (q : Upper.Quartet n) (i : Fin 3) : Prop :=
  P.GraphDisplaysSplit q.1 (Upper.splitOfTopology q i)

/-- Choose a root label canonically from the quartet itself.  This avoids any
global nonemptiness assumption and is available exactly where a displayed
quartet is being queried.-/
def quartetRoot (q : Upper.Quartet n) : Fin n :=
  Upper.quartetEmbedding q 0

/-- The syntax encoding rooted at one of the four labels under consideration.-/
noncomputable def encodeForQuartet
    (P : CanonicalBinaryPhyloGraph (Fin n)) (q : Upper.Quartet n) :
    Tree.PhyloTree (Fin n) :=
  P.encodeAt (quartetRoot q)

end CanonicalBinaryPhyloGraph

namespace GraphQuartet

variable {α V W : Type*} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Deleting corresponding edges commutes with a graph isomorphism.-/
def deleteEdgeIso (e : G ≃g H) (u v : V) :
    G.deleteEdges {s(u, v)} ≃g
      H.deleteEdges {s(e u, e v)} where
  __ := e.toEquiv
  map_rel_iff' := by
    intro x y
    simp only [deleteEdges_adj, Set.mem_singleton_iff]
    change (H.Adj (e x) (e y) ∧ ¬s(e x, e y) = s(e u, e v)) ↔
      (G.Adj x y ∧ ¬s(x, y) = s(u, v))
    rw [e.map_rel_iff]
    constructor
    · rintro ⟨hxy, hne⟩
      refine ⟨hxy, fun heq => hne ?_⟩
      change Sym2.map e s(x, y) = Sym2.map e s(u, v)
      exact congrArg (Sym2.map e) heq
    · rintro ⟨hxy, hne⟩
      refine ⟨hxy, fun heq => hne ?_⟩
      apply Sym2.map.injective e.injective
      simpa only [Sym2.map_mk] using heq

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem deleteEdgeIso_apply (e : G ≃g H) (u v x : V) :
    deleteEdgeIso e u v x = e x :=
  rfl

omit [DecidableEq V] [DecidableEq W] in
/-- Reachability after deleting an edge is invariant under a graph
isomorphism.-/
theorem deleteEdge_reachable_iff (e : G ≃g H) (u v x y : V) :
    (H.deleteEdges {s(e u, e v)}).Reachable (e x) (e y) ↔
      (G.deleteEdges {s(u, v)}).Reachable x y :=
  SimpleGraph.Iso.reachable_iff (φ := deleteEdgeIso e u v)

/-- `ComponentSeparatesAt` is invariant under a pointwise
label-preserving graph isomorphism.-/
theorem componentSeparatesAt_iff_of_iso
    (e : G ≃g H) (labelV : V → Option α) (labelW : W → Option α)
    (hlabel : ∀ x, labelW (e x) = labelV x)
    (u v : V) (A B : Finset α) :
    ComponentSeparatesAt H labelW (e u) (e v) A B ↔
      ComponentSeparatesAt G labelV u v A B := by
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨y, hy, hry⟩ := hA a ha
      let x := e.symm y
      refine ⟨x, ?_, ?_⟩
      · calc
          labelV x = labelW (e x) := (hlabel x).symm
          _ = labelW y := by simp [x]
          _ = some a := hy
      · have := (deleteEdge_reachable_iff e u v u x).mp ?_
        · exact this
        · simpa [x] using hry
    · intro b hb x hx hrx
      have hxe : labelW (e x) = some b := by simpa [hlabel] using hx
      exact hB b hb (e x) hxe
        ((deleteEdge_reachable_iff e u v u x).mpr hrx)
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨x, hx, hrx⟩ := hA a ha
      exact ⟨e x, by simpa [hlabel] using hx,
        (deleteEdge_reachable_iff e u v u x).mpr hrx⟩
    · intro b hb y hy hry
      let x := e.symm y
      have hx : labelV x = some b := by
        calc
          labelV x = labelW (e x) := (hlabel x).symm
          _ = labelW y := by simp [x]
          _ = some b := hy
      apply hB b hb x hx
      apply (deleteEdge_reachable_iff e u v u x).mp
      simpa [x] using hry

/-- The generic edge-separation predicate is invariant under every
label-preserving graph isomorphism.-/
theorem edgeSeparates_iff_of_iso
    (e : G ≃g H) (labelV : V → Option α) (labelW : W → Option α)
    (hlabel : ∀ x, labelW (e x) = labelV x)
    (A B : Finset α) :
    EdgeSeparates H labelW A B ↔ EdgeSeparates G labelV A B := by
  constructor
  · rintro ⟨u', v', huv, hsep⟩
    let u := e.symm u'
    let v := e.symm v'
    refine ⟨u, v, ?_, ?_⟩
    · apply e.map_rel_iff.mp
      simpa [u, v] using huv
    · rcases hsep with hsep | hsep
      · left
        apply (componentSeparatesAt_iff_of_iso e labelV labelW hlabel u v A B).mp
        simpa [u, v] using hsep
      · right
        apply (componentSeparatesAt_iff_of_iso e labelV labelW hlabel u v B A).mp
        simpa [u, v] using hsep
  · rintro ⟨u, v, huv, hsep⟩
    refine ⟨e u, e v, e.map_rel_iff.mpr huv, ?_⟩
    rcases hsep with hsep | hsep
    · left
      exact (componentSeparatesAt_iff_of_iso e labelV labelW hlabel u v A B).mpr hsep
    · right
      exact (componentSeparatesAt_iff_of_iso e labelV labelW hlabel u v B A).mpr hsep

end GraphQuartet

namespace GraphModel.BinaryPhyloGraph

variable {α V : Type*} [Fintype α] [Fintype V] [DecidableEq V]

end GraphModel.BinaryPhyloGraph

namespace CanonicalBinaryPhyloGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Edge separation in a canonical conventional graph is exactly edge
separation in any of its cut-open syntax encodings.-/
theorem edgeSeparates_encodeAt_iff (P : CanonicalBinaryPhyloGraph α)
    (rootLabel : α) (A B : Finset α) :
    GraphQuartet.EdgeSeparates P.tree.G P.tree.leafLabel? A B ↔
      GraphQuartet.EdgeSeparates
        (TreeAdequacy.PhyloTree.graph (P.encodeAt rootLabel))
        (TreeAdequacy.PhyloTree.label? (P.encodeAt rootLabel)) A B := by
  exact GraphQuartet.edgeSeparates_iff_of_iso
    (P.encodeGraphIsoAt rootLabel)
    (TreeAdequacy.PhyloTree.label? (P.encodeAt rootLabel))
    P.tree.leafLabel?
    (P.encodeGraphIsoAt_leafLabel? rootLabel) A B

end CanonicalBinaryPhyloGraph

namespace Tree.PhyloTree

variable {α : Type*} [Fintype α] [DecidableEq α]

end Tree.PhyloTree

namespace CanonicalBinaryPhyloGraph

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The direct display predicate on a conventional graph agrees with the
same direct predicate on every cut-open syntax encoding.-/
theorem graphDisplaysSplit_encodeAt_iff
    (P : CanonicalBinaryPhyloGraph α) (rootLabel : α)
    (Q : Finset α) (s : Circular.QuartetSplit α) :
    P.GraphDisplaysSplit Q s ↔
      GraphQuartet.PhyloTree.GraphDisplaysSplit
        (P.encodeAt rootLabel) Q s := by
  constructor
  · rintro ⟨hs, A, hA, B, hB, hne, hsep⟩
    exact ⟨hs, A, hA, B, hB, hne,
      (P.edgeSeparates_encodeAt_iff rootLabel A B).mp hsep⟩
  · rintro ⟨hs, A, hA, B, hB, hne, hsep⟩
    exact ⟨hs, A, hA, B, hB, hne,
      (P.edgeSeparates_encodeAt_iff rootLabel A B).mpr hsep⟩

end CanonicalBinaryPhyloGraph

namespace Tree.PhyloTree

variable {α : Type} [Fintype α] [DecidableEq α]

end Tree.PhyloTree

end QuartetDistance
