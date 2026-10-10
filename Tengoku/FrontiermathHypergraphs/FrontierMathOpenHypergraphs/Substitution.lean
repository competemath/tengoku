/-
  Support gadgets and the substitution theorem.
-/
import Tengoku
import Tengoku.FrontiermathHypergraphs.FrontierMathOpenHypergraphs.Basic

open Finset

namespace HypergraphLowerBound

/-! ## Support patterns and frames -/

/-- A support pattern on `[t]` is a subset of `Fin t` of size at least `2`. -/
def SupportPattern (t : ℕ) := { S : Finset (Fin t) // 2 ≤ S.card }

/-- The block hypergraphs used in a substitution construction. -/
abbrev BlockFamily (t : ℕ) := HypergraphFamily (Fin t) ℕ

/-- An occurrence of a support pattern in a support multiset. -/
abbrev SupportOcc {t : ℕ} (F : Multiset (SupportPattern t)) := Fin F.card

/-- The support pattern attached to a given support-vertex occurrence. -/
noncomputable def supportPatternAt {t : ℕ}
    (F : Multiset (SupportPattern t)) (s : SupportOcc F) : SupportPattern t :=
  F.toList.get ⟨s.1, by
    rw [Multiset.length_toList]
    exact s.2
  ⟩

/-- The underlying subset of `[t]` attached to a support occurrence. -/
noncomputable def supportSetAt {t : ℕ}
    (F : Multiset (SupportPattern t)) (s : SupportOcc F) : Finset (Fin t) :=
  (supportPatternAt F s).1

/-- `omega_count F T I` counts the occurrences of support patterns `S` in `F`
    with `S ⊆ T` and `|S ∩ I| = 1`, counting multiplicity. -/
noncomputable def omega_count {t : ℕ}
    (F : Multiset (SupportPattern t))
    (T I : Finset (Fin t)) : ℕ :=
  ((Finset.univ : Finset (Fin F.card)).filter fun s =>
      supportSetAt F s ⊆ T ∧ ((supportSetAt F s ∩ I).card = 1)).card

/-- A support multiset `F` is an `n`-frame if the frame inequality holds for every
    `I ⊆ T ⊆ [t]`. -/
def IsFrame {t : ℕ}
    (F : Multiset (SupportPattern t))
    (cap : Fin t → ℕ) : Prop :=
  ∀ T I : Finset (Fin t), I ⊆ T →
    omega_count F T I ≤ (T \ I).sum cap

/-- Vertices of the substituted hypergraph: tagged block vertices together with one
    vertex for each occurrence of a support pattern. -/
inductive SubstVertex (t : ℕ) (F : Multiset (SupportPattern t)) where
  | old (i : Fin t) (v : ℕ)
  | new (s : Fin F.card)
deriving DecidableEq

/-- The substituted hypergraph whose vertices live in `SubstVertex t F`. -/
abbrev SubstitutedHypergraph {t : ℕ} (F : Multiset (SupportPattern t)) :=
  Hypergraph (SubstVertex t F)

/-- The support vertices incident to every edge in block `i`. -/
noncomputable def supportVerticesOnBlock {t : ℕ}
    (F : Multiset (SupportPattern t)) (i : Fin t) : Finset (SubstVertex t F) :=
  ((Finset.univ : Finset (Fin F.card)).filter fun s =>
      i ∈ supportSetAt F s).image
    SubstVertex.new

/-- Lift one edge from block `i` into the substituted hypergraph. -/
noncomputable def liftBlockEdge {t : ℕ}
    (F : Multiset (SupportPattern t)) (i : Fin t) (e : Finset ℕ) :
    Finset (SubstVertex t F) :=
  (e.image fun v => SubstVertex.old i v) ∪ supportVerticesOnBlock F i

/-- The substitution hypergraph `F[G_1, ..., G_t]`, realized as the hypergraph whose
    vertices are tagged block vertices plus support vertices, and whose edges are the
    lifted edges of the blocks. -/
noncomputable def substitutionHypergraph {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t) : SubstitutedHypergraph F :=
  ((Finset.univ : Finset (Fin t)).biUnion fun i =>
    (blocks i).image (liftBlockEdge F i))

/-- The selected edges from block `i` inside a chosen subfamily `P` of the substituted
    hypergraph. -/
noncomputable def selectedBlockEdges {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) : Hypergraph ℕ :=
  (blocks i).filter fun e => liftBlockEdge F i e ∈ P

/-- The number of selected edges from block `i`. -/
noncomputable def selectedBlockCount {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) : ℕ :=
  (selectedBlockEdges F blocks P i).card

/-- The number of selected edges from block `i` containing `v`. -/
noncomputable def selectedOldVertexCount {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) (v : ℕ) : ℕ :=
  ((selectedBlockEdges F blocks P i).filter fun e => v ∈ e).card

/-- The number of selected substituted edges incident to a support occurrence. -/
noncomputable def selectedSupportCount {t : ℕ}
    {F : Multiset (SupportPattern t)}
    (P : SubstitutedHypergraph F) (s : SupportOcc F) : ℕ :=
  (P.filter fun E => SubstVertex.new s ∈ E).card

/-- The blocks from which at most one selected edge is taken. -/
noncomputable def T_of {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter fun i =>
    selectedBlockCount F blocks P i ≤ 1

/-- The blocks from which exactly one selected edge is taken. -/
noncomputable def I_of {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter fun i =>
    selectedBlockCount F blocks P i = 1

/-- The old vertices in block `i` that are seen exactly once by the selected family `P`. -/
noncomputable def oldUniqueVerticesOnBlock {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) : Finset ℕ :=
  (vertexSet (blocks i)).filter fun v =>
    (selectedOldVertexCount F blocks P i v = 1)

/-- The support-vertex occurrences seen exactly once by the selected family `P`. -/
noncomputable def newUniqueSupportVertices {t : ℕ}
    (F : Multiset (SupportPattern t))
    (_blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) : Finset (SupportOcc F) :=
  (Finset.univ : Finset (Fin F.card)).filter fun s =>
    (selectedSupportCount P s = 1)

/-- The uniquely covered old vertices in the substituted hypergraph, grouped blockwise. -/
noncomputable def oldUniqueVertexUnion {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) : Finset (SubstVertex t F) :=
  ((Finset.univ : Finset (Fin t)).biUnion fun i =>
    (oldUniqueVerticesOnBlock F blocks P i).image (SubstVertex.old i))

/-- The uniquely covered support vertices in the substituted hypergraph. -/
noncomputable def newUniqueVertexUnion {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) : Finset (SubstVertex t F) :=
  (newUniqueSupportVertices F blocks P).image SubstVertex.new

/-- The old vertices coming from the block hypergraphs, tagged by their block index. -/
noncomputable def oldVertexUnion {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t) : Finset (SubstVertex t F) :=
  ((Finset.univ : Finset (Fin t)).biUnion fun i =>
    (vertexSet (blocks i)).image (SubstVertex.old i))

/-- All support vertices of the substituted hypergraph, indexed by their occurrences in `F`. -/
noncomputable def allNewVertices {t : ℕ}
    (F : Multiset (SupportPattern t)) : Finset (SubstVertex t F) :=
  (Finset.univ : Finset (Fin F.card)).image SubstVertex.new

@[simp] lemma mem_supportVerticesOnBlock_iff {t : ℕ}
    {F : Multiset (SupportPattern t)} {i : Fin t} {s : SupportOcc F} :
    SubstVertex.new s ∈ supportVerticesOnBlock F i ↔ i ∈ supportSetAt F s := by
  simp [supportVerticesOnBlock]

@[simp] lemma old_mem_liftBlockEdge_iff {t : ℕ}
    {F : Multiset (SupportPattern t)} {i j : Fin t} {v : ℕ} {e : Finset ℕ} :
    SubstVertex.old i v ∈ liftBlockEdge F j e ↔ i = j ∧ v ∈ e := by
  constructor
  · intro h
    rw [liftBlockEdge, Finset.mem_union] at h
    rcases h with h | h
    · rcases Finset.mem_image.mp h with ⟨v', hv', hEq⟩
      lia
    · rcases Finset.mem_image.mp h with ⟨s, hs, hEq⟩
      cases hEq
  · rintro ⟨rfl, hv⟩
    simp [liftBlockEdge, hv]

@[simp] lemma new_mem_liftBlockEdge_iff {t : ℕ}
    {F : Multiset (SupportPattern t)} {s : SupportOcc F} {i : Fin t} {e : Finset ℕ} :
    SubstVertex.new s ∈ liftBlockEdge F i e ↔ i ∈ supportSetAt F s := by
  simp [liftBlockEdge]

lemma liftBlockEdge_injective {t : ℕ}
    (F : Multiset (SupportPattern t)) (i : Fin t) :
    Function.Injective (liftBlockEdge F i) := by
  intro e e' hEq
  ext v
  constructor
  · intro hv
    have hmem : SubstVertex.old i v ∈ liftBlockEdge F i e := by
      simp [hv]
    rw [hEq] at hmem
    simpa using (old_mem_liftBlockEdge_iff.mp hmem).2
  · intro hv
    have hmem : SubstVertex.old i v ∈ liftBlockEdge F i e' := by
      simp [hv]
    rw [← hEq] at hmem
    simpa using (old_mem_liftBlockEdge_iff.mp hmem).2

@[simp] lemma mem_T_of_iff {t : ℕ}
    {F : Multiset (SupportPattern t)}
    {blocks : BlockFamily t}
    {P : SubstitutedHypergraph F} {i : Fin t} :
    i ∈ T_of F blocks P ↔ selectedBlockCount F blocks P i ≤ 1 := by
  simp [T_of]

@[simp] lemma mem_I_of_iff {t : ℕ}
    {F : Multiset (SupportPattern t)}
    {blocks : BlockFamily t}
    {P : SubstitutedHypergraph F} {i : Fin t} :
    i ∈ I_of F blocks P ↔ selectedBlockCount F blocks P i = 1 := by
  simp [I_of]

lemma card_inter_I_of_eq_sum_indicator {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (S : Finset (Fin t)) :
    (S ∩ I_of F blocks P).card =
      ∑ i ∈ S, if selectedBlockCount F blocks P i = 1 then 1 else 0 := by
  rw [show S ∩ I_of F blocks P =
      S.filter (fun i => selectedBlockCount F blocks P i = 1) by
      ext i
      simp [I_of]]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-! ## Substitution theorem -/

/-- The assumptions on a family of block hypergraphs needed for the qualitative
    substitution theorem. -/
structure PartitionedBlocks {t : ℕ}
    (cap : Fin t → ℕ) (blocks : BlockFamily t) : Prop where
  vertexDisjoint : Pairwise fun i j => Disjoint (vertexSet (blocks i)) (vertexSet (blocks j))
  edgeDisjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j)
  partitionBound : ∀ i, NoLargePartition (blocks i) (cap i)

/-- The additional edge/vertex count data needed for the quantitative recurrence. -/
structure CountedBlocks {t : ℕ}
    (edgeCounts vertexCounts : Fin t → ℕ) (blocks : BlockFamily t)
    : Prop extends PartitionedBlocks edgeCounts blocks where
  edgeCard : ∀ i, (blocks i).card = edgeCounts i
  vertexCard : ∀ i, (vertexSet (blocks i)).card = vertexCounts i

end HypergraphLowerBound
