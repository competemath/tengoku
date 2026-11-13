import Tengoku.CkHopfFormalization.GaugeGeometry.Core.Sector
import Tengoku.Seed.Data.Finset.Basic
import Tengoku.Seed.Data.Finset.Card
import Tengoku.Seed.Data.Finset.Lattice.Fold
import Tengoku.Seed.Data.Multiset.Basic
import Tengoku.Seed.Logic.Relation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace GaugeGeometry.QFT.Combinatorial

abbrev GaugeSector := GaugeGeometry.Core.GaugeSector

/--
Vertex labels for combinatorial Feynman graphs.
Version 1 uses natural-number identifiers.-/
abbrev VertexId := Nat

/--
An internal edge of a Feynman graph.

Interpretation:
- `source`, `target` : incident vertices
- `sector`           : gauge-sector label carried by the edge-/
structure FeynmanEdge where
  source : VertexId
  target : VertexId
  sector : GaugeSector
  deriving DecidableEq

/--
An external leg of a Feynman graph.

Interpretation:
- `attachedTo` : the incident vertex
- `sector`     : the sector label carried by the leg-/
structure ExternalLeg where
  attachedTo : VertexId
  sector : GaugeSector
  deriving DecidableEq

/--
A minimal combinatorial Feynman graph.

Version 1 stores:
- a finite vertex set,
- a multiset of internal edges,
- a multiset of external legs.-/
structure FeynmanGraph where
  vertices : Finset VertexId
  internalEdges : Multiset FeynmanEdge
  externalLegs : Multiset ExternalLeg

namespace FeynmanEdge

/--
An internal edge is supported on a vertex set if both endpoints lie in it.-/
def SupportedOn (e : FeynmanEdge) (V : Finset VertexId) : Prop :=
  e.source ∈ V ∧ e.target ∈ V

@[simp] theorem supportedOn_def (e : FeynmanEdge) (V : Finset VertexId) :
    e.SupportedOn V = (e.source ∈ V ∧ e.target ∈ V) := by
  rfl

/--
A self-loop edge.-/
def IsSelfLoop (e : FeynmanEdge) : Prop :=
  e.source = e.target

@[simp] theorem isSelfLoop_def (e : FeynmanEdge) :
    e.IsSelfLoop = (e.source = e.target) := by
  rfl

/--
An edge is incident to vertex `v` if `v` is one of its endpoints.-/
def Incident (e : FeynmanEdge) (v : VertexId) : Prop :=
  e.source = v ∨ e.target = v

@[simp] theorem incident_def (e : FeynmanEdge) (v : VertexId) :
    e.Incident v = (e.source = v ∨ e.target = v) := by
  rfl

/--
For a self-loop edge, incidence collapses to matching the single endpoint.-/
theorem isSelfLoop_incident_iff
    {e : FeynmanEdge} (h : e.IsSelfLoop) (v : VertexId) :
    e.Incident v ↔ e.source = v := by
  unfold Incident
  rw [h]
  exact or_self_iff

/--
H1.3 — **Retarget an edge through a contracted set**.

Given a set of vertices `γ` that are being collapsed to a single new
vertex `star`, rewrite any endpoint of `e` that lies in `γ` to `star`. Other
endpoints are left untouched.

This is one of the three pieces of data that produce the contracted
graph `γ.contract`:
- internal edges of `G` with both endpoints in `γ` are *removed*,
- internal edges crossing the boundary are *retargeted* (here),
- edges entirely outside `γ` are *kept unchanged* (this function acts
  as identity on them).-/
def retarget (γ : Finset VertexId) (star : VertexId) (e : FeynmanEdge) :
    FeynmanEdge where
  source := if e.source ∈ γ then star else e.source
  target := if e.target ∈ γ then star else e.target
  sector := e.sector

@[simp] theorem retarget_source (γ : Finset VertexId) (star : VertexId)
    (e : FeynmanEdge) :
    (e.retarget γ star).source = if e.source ∈ γ then star else e.source := rfl

@[simp] theorem retarget_target (γ : Finset VertexId) (star : VertexId)
    (e : FeynmanEdge) :
    (e.retarget γ star).target = if e.target ∈ γ then star else e.target := rfl

@[simp] theorem retarget_sector (γ : Finset VertexId) (star : VertexId)
    (e : FeynmanEdge) :
    (e.retarget γ star).sector = e.sector := rfl

/-- If neither endpoint of `e` lies in `γ`, retargeting leaves `e` unchanged.-/
theorem retarget_of_not_mem {γ : Finset VertexId} {star : VertexId}
    {e : FeynmanEdge}
    (hs : e.source ∉ γ) (ht : e.target ∉ γ) :
    e.retarget γ star = e := by
  cases e
  simp [retarget, hs, ht]

end FeynmanEdge

namespace ExternalLeg

/--
An external leg is supported on a vertex set if its attachment vertex lies in it.-/
def SupportedOn (ℓ : ExternalLeg) (V : Finset VertexId) : Prop :=
  ℓ.attachedTo ∈ V

@[simp] theorem supportedOn_def (ℓ : ExternalLeg) (V : Finset VertexId) :
    ℓ.SupportedOn V = (ℓ.attachedTo ∈ V) := by
  rfl

/--
H1.4 — **Retarget an external leg through a contracted set**.

Analogue of `FeynmanEdge.retarget`: if `ℓ.attachedTo` lies in the
contracted set `γ`, reattach the leg to the fresh vertex `star`; otherwise
leave it unchanged.-/
def retarget (γ : Finset VertexId) (star : VertexId) (ℓ : ExternalLeg) :
    ExternalLeg where
  attachedTo := if ℓ.attachedTo ∈ γ then star else ℓ.attachedTo
  sector := ℓ.sector

@[simp] theorem retarget_attachedTo (γ : Finset VertexId) (star : VertexId)
    (ℓ : ExternalLeg) :
    (ℓ.retarget γ star).attachedTo =
      if ℓ.attachedTo ∈ γ then star else ℓ.attachedTo := rfl

@[simp] theorem retarget_sector (γ : Finset VertexId) (star : VertexId)
    (ℓ : ExternalLeg) :
    (ℓ.retarget γ star).sector = ℓ.sector := rfl

/-- If `ℓ`'s attachment is outside `γ`, retargeting leaves `ℓ` unchanged.-/
theorem retarget_of_not_mem {γ : Finset VertexId} {star : VertexId}
    {ℓ : ExternalLeg} (h : ℓ.attachedTo ∉ γ) :
    ℓ.retarget γ star = ℓ := by
  cases ℓ
  simp [retarget, h]

end ExternalLeg

namespace FeynmanGraph

/--
Basic well-formedness for combinatorial Feynman graphs:
all internal-edge endpoints and all external-leg attachments
must lie in the chosen vertex set.-/
def WellFormed (G : FeynmanGraph) : Prop :=
  (∀ e ∈ G.internalEdges, e.SupportedOn G.vertices) ∧
  (∀ ℓ ∈ G.externalLegs, ℓ.SupportedOn G.vertices)

/--
Number of vertices.-/
def vertexCount (G : FeynmanGraph) : Nat :=
  G.vertices.card

/--
Number of internal edges, counted with multiplicity.-/
def internalEdgeCount (G : FeynmanGraph) : Nat :=
  G.internalEdges.card

/--
Number of external legs, counted with multiplicity.-/
def externalLegCount (G : FeynmanGraph) : Nat :=
  G.externalLegs.card

/--
The empty combinatorial Feynman graph.-/
def emptyGraph : FeynmanGraph where
  vertices := ∅
  internalEdges := 0
  externalLegs := 0

@[simp] theorem emptyGraph_vertices :
    emptyGraph.vertices = ∅ := by
  rfl

@[simp] theorem emptyGraph_internalEdges :
    emptyGraph.internalEdges = 0 := by
  rfl

@[simp] theorem emptyGraph_externalLegs :
    emptyGraph.externalLegs = 0 := by
  rfl

@[simp] theorem emptyGraph_vertexCount :
    emptyGraph.vertexCount = 0 := by
  simp [vertexCount]

@[simp] theorem emptyGraph_internalEdgeCount :
    emptyGraph.internalEdgeCount = 0 := by
  rfl

@[simp] theorem emptyGraph_externalLegCount :
    emptyGraph.externalLegCount = 0 := by
  rfl

theorem emptyGraph_wellFormed :
    emptyGraph.WellFormed := by
  constructor
  · intro e he
    simp at he
  · intro ℓ hℓ
    simp at hℓ

theorem wellFormed_internal
    {G : FeynmanGraph} (hG : G.WellFormed)
    {e : FeynmanEdge} (he : e ∈ G.internalEdges) :
    e.SupportedOn G.vertices := by
  exact hG.1 e he

theorem wellFormed_external
    {G : FeynmanGraph} (hG : G.WellFormed)
    {ℓ : ExternalLeg} (hℓ : ℓ ∈ G.externalLegs) :
    ℓ.SupportedOn G.vertices := by
  exact hG.2 ℓ hℓ

@[simp] theorem FeynmanGraph_eta (G : FeynmanGraph) :
    FeynmanGraph.mk G.vertices G.internalEdges G.externalLegs = G := by
  cases G
  rfl

/--
Two vertices are adjacent in `G` if there is an internal edge of `G`
connecting them (in either orientation).-/
def Adjacent (G : FeynmanGraph) (u v : VertexId) : Prop :=
  ∃ e ∈ G.internalEdges,
    (e.source = u ∧ e.target = v) ∨ (e.source = v ∧ e.target = u)

/--
Reachability in `G` is the reflexive-transitive closure of `Adjacent`.-/
def Reachable (G : FeynmanGraph) (u v : VertexId) : Prop :=
  Relation.ReflTransGen G.Adjacent u v

/--
`G` is connected if every pair of vertices in `G.vertices` is reachable.-/
def IsConnected (G : FeynmanGraph) : Prop :=
  ∀ ⦃u v⦄, u ∈ G.vertices → v ∈ G.vertices → G.Reachable u v

/--
The Euler-type loop number `L(G) = E - V + 1`, taken in `Int`
to avoid truncation when `E < V - 1`.-/
def loopNumber (G : FeynmanGraph) : Int :=
  (G.internalEdgeCount : Int) - (G.vertexCount : Int) + 1

/--
Number of internal edges carrying a given gauge sector,
counted with multiplicity.-/
def internalEdgeCountBy (G : FeynmanGraph) (s : GaugeSector) : Nat :=
  (G.internalEdges.filter (·.sector = s)).card

/--
Number of external legs carrying a given gauge sector,
counted with multiplicity.-/
def externalLegCountBy (G : FeynmanGraph) (s : GaugeSector) : Nat :=
  (G.externalLegs.filter (·.sector = s)).card

/--
Sector-wise decomposition of the total internal-edge count:
summing the sector-indexed counts over the three canonical sectors
reconstructs `internalEdgeCount`.-/
theorem internalEdgeCount_eq_sum_sectors (G : FeynmanGraph) :
    G.internalEdgeCount =
      G.internalEdgeCountBy GaugeGeometry.Core.GaugeSector.hypercharge
      + G.internalEdgeCountBy GaugeGeometry.Core.GaugeSector.weak
      + G.internalEdgeCountBy GaugeGeometry.Core.GaugeSector.color := by
  classical
  unfold internalEdgeCount internalEdgeCountBy
  refine Multiset.induction_on G.internalEdges ?_ ?_
  · simp
  · intro e s ih
    cases hsec : e.sector <;>
      simp [Multiset.filter_cons_of_pos, Multiset.filter_cons_of_neg,
            hsec, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/--
Sector-wise decomposition of the total external-leg count:
summing the sector-indexed counts over the three canonical sectors
reconstructs `externalLegCount`.-/
theorem externalLegCount_eq_sum_sectors (G : FeynmanGraph) :
    G.externalLegCount =
      G.externalLegCountBy GaugeGeometry.Core.GaugeSector.hypercharge
      + G.externalLegCountBy GaugeGeometry.Core.GaugeSector.weak
      + G.externalLegCountBy GaugeGeometry.Core.GaugeSector.color := by
  classical
  unfold externalLegCount externalLegCountBy
  refine Multiset.induction_on G.externalLegs ?_ ?_
  · simp
  · intro ℓ s ih
    cases hsec : ℓ.sector <;>
      simp [Multiset.filter_cons_of_pos, Multiset.filter_cons_of_neg,
            hsec, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/--
Strong one-loop predicate: connected, nonempty, with Euler loop
number equal to one.

The nonemptiness clause `0 < G.vertexCount` excludes the vacuous
case where the empty graph satisfies `loopNumber = 0 - 0 + 1 = 1`
while carrying no actual one-loop content.-/
def IsOneLoopStrong (G : FeynmanGraph) : Prop :=
  G.IsConnected ∧ 0 < G.vertexCount ∧ G.loopNumber = 1

/--
H0.1 — Erase a single internal edge from `G`.

The vertex set and external legs are unchanged; only one occurrence of
`e` (counted with multiplicity) is removed from `G.internalEdges` via
`Multiset.erase`.

If `e ∉ G.internalEdges`, the result equals `G` (this mirrors
`Multiset.erase_of_not_mem`).-/
def eraseInternalEdge (G : FeynmanGraph) (e : FeynmanEdge) : FeynmanGraph where
  vertices := G.vertices
  internalEdges := G.internalEdges.erase e
  externalLegs := G.externalLegs

@[simp] theorem eraseInternalEdge_vertices (G : FeynmanGraph) (e : FeynmanEdge) :
    (G.eraseInternalEdge e).vertices = G.vertices := rfl

@[simp] theorem eraseInternalEdge_internalEdges (G : FeynmanGraph) (e : FeynmanEdge) :
    (G.eraseInternalEdge e).internalEdges = G.internalEdges.erase e := rfl

@[simp] theorem eraseInternalEdge_externalLegs (G : FeynmanGraph) (e : FeynmanEdge) :
    (G.eraseInternalEdge e).externalLegs = G.externalLegs := rfl

/--
H0.2 — Erasing an internal edge that is actually present strictly
decreases the internal-edge count.

This is the key termination fact underlying bridge elimination and the
well-founded recursion on `loopNumber` used by the coproduct.-/
theorem eraseInternalEdge_internalEdgeCount_lt
    {G : FeynmanGraph} {e : FeynmanEdge} (he : e ∈ G.internalEdges) :
    (G.eraseInternalEdge e).internalEdgeCount < G.internalEdgeCount := by
  have hpos : 0 < G.internalEdges.card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨e, he⟩
  unfold internalEdgeCount
  rw [eraseInternalEdge_internalEdges, Multiset.card_erase_of_mem he]
  exact Nat.sub_lt hpos Nat.one_pos

/-!
### H1.1 — Fresh-vertex generation

For the subgraph contraction operation we need a `VertexId` that does
not appear in a given finite set of vertices. Since `VertexId = Nat`,
taking the maximum of the set (with `⊥ = 0` fallback for the empty
case, supplied by `Finset.sup`) and adding one yields a fresh vertex
in one step.
-/

/--
H1.1 — **Fresh vertex generator**: for any `V : Finset VertexId`, returns
a `VertexId` not contained in `V`.

Implementation: `V.sup id + 1`. On the empty set `V.sup id = 0`, so
`freshVertex ∅ = 1`. On nonempty sets, it is strictly greater than
every element of `V` (see `freshVertex_not_mem`).-/
def freshVertex (V : Finset VertexId) : VertexId :=
  V.sup id + 1

/--
H1.2 — `freshVertex V` never belongs to `V`: every element of `V` is
bounded above by `V.sup id`, so the successor `V.sup id + 1` is strictly
greater than all of them.-/
theorem freshVertex_not_mem (V : Finset VertexId) :
    freshVertex V ∉ V := by
  intro hmem
  have hle : V.sup id + 1 ≤ V.sup id := by
    have : id (V.sup id + 1) ≤ V.sup id := Finset.le_sup (f := id) hmem
    simpa using this
  exact Nat.not_succ_le_self _ hle

end FeynmanGraph

end GaugeGeometry.QFT.Combinatorial
