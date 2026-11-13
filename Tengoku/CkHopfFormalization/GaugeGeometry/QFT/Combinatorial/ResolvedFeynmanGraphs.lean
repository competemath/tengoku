import Tengoku.CkHopfFormalization.GaugeGeometry.QFT.Combinatorial.FeynmanGraphs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boundary-resolved Feynman graphs (Track R)

The flat `FeynmanGraph` carrier identifies an internal edge with its
`(source, target, sector)` triple and an external leg with its
`(attachedTo, sector)` pair (`deriving DecidableEq`).  Under contraction to a
single star vertex, distinct edges/legs with the same retargeted endpoints
collapse — this is the root of the two boundary-semantics facades
(`PromotedExternalLegsLiftableModel`, `ForestGraphInsertionUniquenessModel`),
both shown FALSE on the flat carrier by explicit counterexamples.

This file introduces a **boundary-resolved** carrier: edges and legs carry an
identity (`ResolvedEdgeId` / `ResolvedLegId`) that survives contraction, so the
retarget map is identity-preserving (hence injective on residuals) and leg
preimages are canonical.  The two facades become *theorems* here.

A forgetful map `forget : ResolvedFeynmanGraph → FeynmanGraph` drops the
identities, linking the two carriers: the flat carrier is the forgetful image,
and the suppressed identity data is exactly what the two facades assume.

This is **Track R-1a**: the resolved carrier core + forgetful map only.
Contraction, identity-uniqueness predicates, and facade discharge follow in
later sprints.  Existing definitions are not modified.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- Identity tag for a boundary-resolved internal edge.  Survives contraction,
so two edges that retarget to the same endpoints stay distinguishable.-/
structure ResolvedEdgeId where
  id : Nat
  deriving DecidableEq, Repr

/-- Identity tag for a boundary-resolved external leg.-/
structure ResolvedLegId where
  id : Nat
  deriving DecidableEq, Repr

/-- A boundary-resolved internal edge: the flat `(source, target, sector)` data
plus a persistent `edgeId`.-/
structure ResolvedFeynmanEdge where
  edgeId : ResolvedEdgeId
  source : VertexId
  target : VertexId
  sector : GaugeSector
  deriving DecidableEq, Repr

/-- A boundary-resolved external leg: the flat `(attachedTo, sector)` data plus
a persistent `legId`.-/
structure ResolvedExternalLeg where
  legId : ResolvedLegId
  attachedTo : VertexId
  sector : GaugeSector
  deriving DecidableEq, Repr

/-- A boundary-resolved Feynman graph: same shape as `FeynmanGraph` but over the
resolved edge/leg carriers.-/
structure ResolvedFeynmanGraph where
  vertices : Finset VertexId
  internalEdges : Multiset ResolvedFeynmanEdge
  externalLegs : Multiset ResolvedExternalLeg

namespace ResolvedFeynmanEdge

/-- Forget the edge identity, recovering a flat `FeynmanEdge`.-/
def forget (e : ResolvedFeynmanEdge) : FeynmanEdge :=
  { source := e.source, target := e.target, sector := e.sector }

@[simp] theorem forget_source (e : ResolvedFeynmanEdge) :
    e.forget.source = e.source := rfl

@[simp] theorem forget_target (e : ResolvedFeynmanEdge) :
    e.forget.target = e.target := rfl

@[simp] theorem forget_sector (e : ResolvedFeynmanEdge) :
    e.forget.sector = e.sector := rfl

end ResolvedFeynmanEdge

namespace ResolvedExternalLeg

/-- Forget the leg identity, recovering a flat `ExternalLeg`.-/
def forget (ℓ : ResolvedExternalLeg) : ExternalLeg :=
  { attachedTo := ℓ.attachedTo, sector := ℓ.sector }

@[simp] theorem forget_attachedTo (ℓ : ResolvedExternalLeg) :
    ℓ.forget.attachedTo = ℓ.attachedTo := rfl

@[simp] theorem forget_sector (ℓ : ResolvedExternalLeg) :
    ℓ.forget.sector = ℓ.sector := rfl

end ResolvedExternalLeg

namespace ResolvedFeynmanGraph

/-- Forget all identities, recovering a flat `FeynmanGraph`.-/
def forget (G : ResolvedFeynmanGraph) : FeynmanGraph :=
  { vertices := G.vertices
    internalEdges := G.internalEdges.map ResolvedFeynmanEdge.forget
    externalLegs := G.externalLegs.map ResolvedExternalLeg.forget }

@[simp] theorem forget_vertices (G : ResolvedFeynmanGraph) :
    G.forget.vertices = G.vertices := rfl

@[simp] theorem forget_internalEdges (G : ResolvedFeynmanGraph) :
    G.forget.internalEdges = G.internalEdges.map ResolvedFeynmanEdge.forget := rfl

@[simp] theorem forget_externalLegs (G : ResolvedFeynmanGraph) :
    G.forget.externalLegs = G.externalLegs.map ResolvedExternalLeg.forget := rfl

end ResolvedFeynmanGraph

/-! ## Track R-1b — identity-preserving retarget + injectivity

The crux of "the bombs disappear": the resolved retarget rewrites endpoints by
a vertex map `f` (the contraction's `retargetVertex`) but **preserves the
identity tag**.  When the graph's identity tags are unique, two edges/legs with
equal retargets must have equal tags, hence are equal — `retarget` is injective
on the graph's components even when `f` is many-to-one (the flat-carrier
collapse). -/

namespace ResolvedFeynmanEdge

/-- Identity-preserving endpoint retarget along a vertex map `f` (the
contraction's `retargetVertex`).  Unlike the flat `FeynmanEdge.retarget`, the
`edgeId` is carried through unchanged.-/
def retarget (f : VertexId → VertexId) (e : ResolvedFeynmanEdge) :
    ResolvedFeynmanEdge :=
  { edgeId := e.edgeId
    source := f e.source
    target := f e.target
    sector := e.sector }

@[simp] theorem retarget_edgeId (f : VertexId → VertexId)
    (e : ResolvedFeynmanEdge) : (e.retarget f).edgeId = e.edgeId := rfl

@[simp] theorem retarget_source (f : VertexId → VertexId)
    (e : ResolvedFeynmanEdge) : (e.retarget f).source = f e.source := rfl

@[simp] theorem retarget_target (f : VertexId → VertexId)
    (e : ResolvedFeynmanEdge) : (e.retarget f).target = f e.target := rfl

@[simp] theorem retarget_sector (f : VertexId → VertexId)
    (e : ResolvedFeynmanEdge) : (e.retarget f).sector = e.sector := rfl

end ResolvedFeynmanEdge

namespace ResolvedExternalLeg

/-- Identity-preserving attachment retarget along a vertex map `f`.-/
def retarget (f : VertexId → VertexId) (ℓ : ResolvedExternalLeg) :
    ResolvedExternalLeg :=
  { legId := ℓ.legId
    attachedTo := f ℓ.attachedTo
    sector := ℓ.sector }

@[simp] theorem retarget_legId (f : VertexId → VertexId)
    (ℓ : ResolvedExternalLeg) : (ℓ.retarget f).legId = ℓ.legId := rfl

@[simp] theorem retarget_attachedTo (f : VertexId → VertexId)
    (ℓ : ResolvedExternalLeg) : (ℓ.retarget f).attachedTo = f ℓ.attachedTo := rfl

@[simp] theorem retarget_sector (f : VertexId → VertexId)
    (ℓ : ResolvedExternalLeg) : (ℓ.retarget f).sector = ℓ.sector := rfl

end ResolvedExternalLeg

namespace ResolvedFeynmanGraph

/-- The internal edges of `G` have pairwise-distinct `edgeId`s.-/
def EdgeIdsUnique (G : ResolvedFeynmanGraph) : Prop :=
  ∀ e₁ ∈ G.internalEdges, ∀ e₂ ∈ G.internalEdges,
    e₁.edgeId = e₂.edgeId → e₁ = e₂

/-- The external legs of `G` have pairwise-distinct `legId`s.-/
def LegIdsUnique (G : ResolvedFeynmanGraph) : Prop :=
  ∀ ℓ₁ ∈ G.externalLegs, ∀ ℓ₂ ∈ G.externalLegs,
    ℓ₁.legId = ℓ₂.legId → ℓ₁ = ℓ₂

end ResolvedFeynmanGraph

/-- **Bomb-defusal core (edges).**  Under id-uniqueness, the identity-preserving
retarget is injective on `G`'s internal edges — even when the vertex map `f`
collapses distinct endpoints (the flat-carrier failure mode).-/
theorem ResolvedFeynmanEdge.eq_of_retarget_eq_of_id_unique
    {G : ResolvedFeynmanGraph} (hId : G.EdgeIdsUnique)
    {f : VertexId → VertexId} {e₁ e₂ : ResolvedFeynmanEdge}
    (he₁ : e₁ ∈ G.internalEdges) (he₂ : e₂ ∈ G.internalEdges)
    (h : e₁.retarget f = e₂.retarget f) :
    e₁ = e₂ := by
  apply hId e₁ he₁ e₂ he₂
  simpa using congrArg ResolvedFeynmanEdge.edgeId h

/-- **Bomb-defusal core (legs).**  Under id-uniqueness, the identity-preserving
retarget is injective on `G`'s external legs.-/
theorem ResolvedExternalLeg.eq_of_retarget_eq_of_id_unique
    {G : ResolvedFeynmanGraph} (hId : G.LegIdsUnique)
    {f : VertexId → VertexId} {ℓ₁ ℓ₂ : ResolvedExternalLeg}
    (hℓ₁ : ℓ₁ ∈ G.externalLegs) (hℓ₂ : ℓ₂ ∈ G.externalLegs)
    (h : ℓ₁.retarget f = ℓ₂.retarget f) :
    ℓ₁ = ℓ₂ := by
  apply hId ℓ₁ hℓ₁ ℓ₂ hℓ₂
  simpa using congrArg ResolvedExternalLeg.legId h

/-- Forgetful compatibility: the resolved retarget along `f` projects to the
flat endpoint rewrite (`forget` commutes with retarget at the data level).
Stated as the endpoint/sector equalities, since the flat `FeynmanEdge.retarget`
uses a `(Finset, star)` signature rather than a vertex map.-/
@[simp] theorem ResolvedFeynmanEdge.forget_retarget
    (f : VertexId → VertexId) (e : ResolvedFeynmanEdge) :
    (e.retarget f).forget =
      { source := f e.source, target := f e.target, sector := e.sector } := rfl

@[simp] theorem ResolvedExternalLeg.forget_retarget
    (f : VertexId → VertexId) (ℓ : ResolvedExternalLeg) :
    (ℓ.retarget f).forget =
      { attachedTo := f ℓ.attachedTo, sector := ℓ.sector } := rfl

/-! ## Track R-2a — graph-level identity-preserving contraction

Lift the identity-preserving retarget to the whole graph: contract by rewriting
every endpoint through a vertex map `f` (the contraction's `retargetVertex`)
while carrying all edge/leg identities through.  The forgetful image is the flat
retargeted edge/leg multisets, and identity-uniqueness lifts to injectivity of
the retarget map on the graph's components. -/

namespace ResolvedFeynmanGraph

/-- Retarget all internal edges of `G` through `f`, preserving `edgeId`s.-/
def retargetInternalEdges (G : ResolvedFeynmanGraph) (f : VertexId → VertexId) :
    Multiset ResolvedFeynmanEdge :=
  G.internalEdges.map (ResolvedFeynmanEdge.retarget f)

/-- Retarget all external legs of `G` through `f`, preserving `legId`s.-/
def retargetExternalLegs (G : ResolvedFeynmanGraph) (f : VertexId → VertexId) :
    Multiset ResolvedExternalLeg :=
  G.externalLegs.map (ResolvedExternalLeg.retarget f)

/-- Identity-preserving contracted/retargeted graph: rewrite endpoints by `f`
onto the caller-supplied vertex carrier `V`, carrying all identities through.-/
def retargetGraph (G : ResolvedFeynmanGraph) (f : VertexId → VertexId)
    (V : Finset VertexId) : ResolvedFeynmanGraph :=
  { vertices := V
    internalEdges := G.retargetInternalEdges f
    externalLegs := G.retargetExternalLegs f }

@[simp] theorem retargetGraph_vertices (G : ResolvedFeynmanGraph)
    (f : VertexId → VertexId) (V : Finset VertexId) :
    (G.retargetGraph f V).vertices = V := rfl

@[simp] theorem retargetGraph_internalEdges (G : ResolvedFeynmanGraph)
    (f : VertexId → VertexId) (V : Finset VertexId) :
    (G.retargetGraph f V).internalEdges = G.retargetInternalEdges f := rfl

@[simp] theorem retargetGraph_externalLegs (G : ResolvedFeynmanGraph)
    (f : VertexId → VertexId) (V : Finset VertexId) :
    (G.retargetGraph f V).externalLegs = G.retargetExternalLegs f := rfl

/-- Forgetful compatibility: the resolved internal-edge retarget projects to the
flat endpoint rewrite, edgewise.-/
theorem forget_retargetInternalEdges (G : ResolvedFeynmanGraph)
    (f : VertexId → VertexId) :
    (G.retargetInternalEdges f).map ResolvedFeynmanEdge.forget =
      (G.internalEdges.map ResolvedFeynmanEdge.forget).map
        (fun e => { source := f e.source, target := f e.target, sector := e.sector }) := by
  unfold retargetInternalEdges
  rw [Multiset.map_map, Multiset.map_map]
  rfl

theorem forget_retargetExternalLegs (G : ResolvedFeynmanGraph)
    (f : VertexId → VertexId) :
    (G.retargetExternalLegs f).map ResolvedExternalLeg.forget =
      (G.externalLegs.map ResolvedExternalLeg.forget).map
        (fun ℓ => { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }) := by
  unfold retargetExternalLegs
  rw [Multiset.map_map, Multiset.map_map]
  rfl

/-- **Track R-4-link — forgetful map commutes with the identity-preserving
contraction.**  Forgetting the resolved retargeted graph yields the flat graph
whose edges/legs have their endpoints rewritten by `f`.  This is the JAR
diagram: the flat carrier is the *forgetful image* of the resolved carrier, and
the boundary identities (`edgeId`/`legId`) — whose loss under `forget` is
exactly the two semantic facades — are precisely what `forget` discards.  The
resolved contraction is injective (R-3); its flat image (this theorem) is the
lossy flat contraction.-/
theorem forget_retargetGraph (G : ResolvedFeynmanGraph)
    (f : VertexId → VertexId) (V : Finset VertexId) :
    (G.retargetGraph f V).forget =
      { vertices := V
        internalEdges := G.forget.internalEdges.map
          (fun e => { source := f e.source, target := f e.target, sector := e.sector })
        externalLegs := G.forget.externalLegs.map
          (fun ℓ => { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }) } := by
  show ResolvedFeynmanGraph.forget _ = _
  unfold ResolvedFeynmanGraph.forget
  congr 1
  · show (G.retargetInternalEdges f).map ResolvedFeynmanEdge.forget = _
    rw [forget_retargetInternalEdges]
  · show (G.retargetExternalLegs f).map ResolvedExternalLeg.forget = _
    rw [forget_retargetExternalLegs]

/-- **Bomb-defusal at graph level (edges).**  Under id-uniqueness, the retarget
map is injective on `G`'s internal edges (as a function `{e // e ∈ ...} → _`),
so the contracted edge multiset has the same cardinality and no collapse —
unlike the flat carrier.-/
theorem retargetInternalEdges_injOn (G : ResolvedFeynmanGraph)
    (hId : G.EdgeIdsUnique) {f : VertexId → VertexId}
    {e₁ e₂ : ResolvedFeynmanEdge}
    (he₁ : e₁ ∈ G.internalEdges) (he₂ : e₂ ∈ G.internalEdges)
    (h : e₁.retarget f = e₂.retarget f) :
    e₁ = e₂ :=
  ResolvedFeynmanEdge.eq_of_retarget_eq_of_id_unique hId he₁ he₂ h

/-- **Bomb-defusal at graph level (legs).**-/
theorem retargetExternalLegs_injOn (G : ResolvedFeynmanGraph)
    (hId : G.LegIdsUnique) {f : VertexId → VertexId}
    {ℓ₁ ℓ₂ : ResolvedExternalLeg}
    (hℓ₁ : ℓ₁ ∈ G.externalLegs) (hℓ₂ : ℓ₂ ∈ G.externalLegs)
    (h : ℓ₁.retarget f = ℓ₂.retarget f) :
    ℓ₁ = ℓ₂ :=
  ResolvedExternalLeg.eq_of_retarget_eq_of_id_unique hId hℓ₁ hℓ₂ h

end ResolvedFeynmanGraph

/-! ## Track R-3a — submultiset retarget injectivity (CK insertion-uniqueness core)

The flat counterexample (two edges `(a,w),(b,w)` collapsing to `(star,w)`)
disappears at the *multiset* level: under identity-uniqueness, the retarget map
is injective on submultisets of `G`'s components.  This is the resolved-carrier
core that turns `ForestGraphInsertionUniquenessModel` into a theorem. -/

/-- Generic `InjOn`-flavoured multiset map injectivity (not in Mathlib, which
only has the globally-injective `Multiset.map_injective`).  If `f` is injective
on the elements of an ambient `S`, then `map f` is injective on submultisets of
`S`.  Proof: `count` extensionality via `Multiset.count_map_eq_count`.-/
theorem Multiset.map_eq_of_injOn_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {S M₁ M₂ : Multiset α}
    (hInj : Set.InjOn f {x | x ∈ S})
    (hM₁ : M₁ ≤ S) (hM₂ : M₂ ≤ S)
    (h : M₁.map f = M₂.map f) :
    M₁ = M₂ := by
  -- key: for any submultiset M ≤ S and x ∈ S, count x M = (M.map f).count (f x).
  have key : ∀ (M : Multiset α), M ≤ S → ∀ x, x ∈ S →
      (M.map f).count (f x) = M.count x := by
    intro M hM x hxS
    by_cases hxM : x ∈ M
    · exact Multiset.count_map_eq_count f M
        (hInj.mono (fun a ha => Multiset.mem_of_le hM ha)) x hxM
    · rw [Multiset.count_eq_zero.mpr hxM, Multiset.count_map,
        Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro a haM hfa
      apply hxM
      rw [hInj hxS (Multiset.mem_of_le hM haM) hfa]
      exact haM
  rw [Multiset.ext]
  intro x
  by_cases hxS : x ∈ S
  · rw [← key M₁ hM₁ x hxS, ← key M₂ hM₂ x hxS, h]
  · rw [Multiset.count_eq_zero.mpr (fun hx => hxS (Multiset.mem_of_le hM₁ hx)),
        Multiset.count_eq_zero.mpr (fun hx => hxS (Multiset.mem_of_le hM₂ hx))]

/-- **CK insertion-uniqueness core (internal edges).**  Under `EdgeIdsUnique`,
the resolved retarget is injective on submultisets of `G.internalEdges`: two
sub-forests with the same contracted (retargeted) internal-edge multiset have
the *same* internal edges.  The flat counterexample cannot occur — the `edgeId`
survives the collapse.-/
theorem ResolvedFeynmanGraph.retargetInternalEdges_injective_on_submultisets
    (G : ResolvedFeynmanGraph) (hId : G.EdgeIdsUnique) {f : VertexId → VertexId}
    {M₁ M₂ : Multiset ResolvedFeynmanEdge}
    (hM₁ : M₁ ≤ G.internalEdges) (hM₂ : M₂ ≤ G.internalEdges)
    (h : M₁.map (ResolvedFeynmanEdge.retarget f) =
      M₂.map (ResolvedFeynmanEdge.retarget f)) :
    M₁ = M₂ :=
  Multiset.map_eq_of_injOn_le (f := ResolvedFeynmanEdge.retarget f)
    (S := G.internalEdges)
    (fun _e₁ he₁ _e₂ he₂ heq =>
      ResolvedFeynmanEdge.eq_of_retarget_eq_of_id_unique hId he₁ he₂ heq)
    hM₁ hM₂ h

/-- **CK insertion-uniqueness core (external legs).**  Under `LegIdsUnique`,
the resolved retarget is injective on submultisets of `G.externalLegs`.-/
theorem ResolvedFeynmanGraph.retargetExternalLegs_injective_on_submultisets
    (G : ResolvedFeynmanGraph) (hId : G.LegIdsUnique) {f : VertexId → VertexId}
    {M₁ M₂ : Multiset ResolvedExternalLeg}
    (hM₁ : M₁ ≤ G.externalLegs) (hM₂ : M₂ ≤ G.externalLegs)
    (h : M₁.map (ResolvedExternalLeg.retarget f) =
      M₂.map (ResolvedExternalLeg.retarget f)) :
    M₁ = M₂ :=
  Multiset.map_eq_of_injOn_le (f := ResolvedExternalLeg.retarget f)
    (S := G.externalLegs)
    (fun _ℓ₁ hℓ₁ _ℓ₂ hℓ₂ heq =>
      ResolvedExternalLeg.eq_of_retarget_eq_of_id_unique hId hℓ₁ hℓ₂ heq)
    hM₁ hM₂ h

end GaugeGeometry.QFT.Combinatorial
