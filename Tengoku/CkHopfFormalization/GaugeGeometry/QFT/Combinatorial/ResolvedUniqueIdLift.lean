import Tengoku.CkHopfFormalization.GaugeGeometry.QFT.Combinatorial.ResolvedFeynmanGraphs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unique-id resolved lift (Track R-4-superfull scout)

Whereas the constant-id lift (`ofFlatGraph`, Phase 6c) sufficed for the coproduct
equality, the *repair* theorems (`parent_eq_of_remainder_eq`,
`externalLegs_lift_unique`) need `EdgeIdsUnique` / `LegIdsUnique`.  This file
constructs a **unique-id** resolved lift of every flat graph by tagging each
multiset occurrence with its position index (`List.zipIdx` on a chosen list
representative), and proves the forget round-trip and id-uniqueness.

This answers the R-4-superfull knife-edge scout: an `EdgeIdsUnique`/`LegIdsUnique`
resolved lift of every flat `FeynmanGraph` exists.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- Tag each occurrence of a flat edge multiset with its position index.-/
noncomputable def uniqueIdEdges (s : Multiset FeynmanEdge) : Multiset ResolvedFeynmanEdge :=
  (s.toList.zipIdx.map fun p =>
    ({ edgeId := ⟨p.2⟩, source := p.1.source, target := p.1.target,
        sector := p.1.sector } : ResolvedFeynmanEdge) : List ResolvedFeynmanEdge)

/-- Tag each occurrence of a flat leg multiset with its position index.-/
noncomputable def uniqueIdLegs (s : Multiset ExternalLeg) : Multiset ResolvedExternalLeg :=
  (s.toList.zipIdx.map fun p =>
    ({ legId := ⟨p.2⟩, attachedTo := p.1.attachedTo,
        sector := p.1.sector } : ResolvedExternalLeg) : List ResolvedExternalLeg)

/-- Forgetting recovers the original edge multiset.-/
theorem map_forget_uniqueIdEdges (s : Multiset FeynmanEdge) :
    (uniqueIdEdges s).map ResolvedFeynmanEdge.forget = s := by
  unfold uniqueIdEdges
  rw [Multiset.map_coe, List.map_map,
    show (ResolvedFeynmanEdge.forget ∘ fun p : FeynmanEdge × Nat =>
        ({ edgeId := ⟨p.2⟩, source := p.1.source, target := p.1.target,
            sector := p.1.sector } : ResolvedFeynmanEdge)) = Prod.fst from rfl,
    List.zipIdx_map_fst, Multiset.coe_toList]

/-- Forgetting recovers the original leg multiset.-/
theorem map_forget_uniqueIdLegs (s : Multiset ExternalLeg) :
    (uniqueIdLegs s).map ResolvedExternalLeg.forget = s := by
  unfold uniqueIdLegs
  rw [Multiset.map_coe, List.map_map,
    show (ResolvedExternalLeg.forget ∘ fun p : ExternalLeg × Nat =>
        ({ legId := ⟨p.2⟩, attachedTo := p.1.attachedTo,
            sector := p.1.sector } : ResolvedExternalLeg)) = Prod.fst from rfl,
    List.zipIdx_map_fst, Multiset.coe_toList]

/-- The unique-id edge tags have pairwise-distinct `edgeId`s: position index.-/
theorem uniqueIdEdges_idUnique (s : Multiset FeynmanEdge) :
    ∀ e₁ ∈ uniqueIdEdges s, ∀ e₂ ∈ uniqueIdEdges s,
      e₁.edgeId = e₂.edgeId → e₁ = e₂ := by
  intro e₁ he₁ e₂ he₂ hid
  simp only [uniqueIdEdges, Multiset.mem_coe, List.mem_map] at he₁ he₂
  obtain ⟨p₁, hp₁, rfl⟩ := he₁
  obtain ⟨p₂, hp₂, rfl⟩ := he₂
  have hi : p₁.2 = p₂.2 := congrArg ResolvedEdgeId.id hid
  have g₁ := (List.mem_zipIdx_iff_getElem?).mp hp₁
  have g₂ := (List.mem_zipIdx_iff_getElem?).mp hp₂
  rw [hi, g₂] at g₁
  have : p₁.1 = p₂.1 := (Option.some.injEq _ _).mp g₁.symm
  simp only [this, hi]

/-- The unique-id leg tags have pairwise-distinct `legId`s.-/
theorem uniqueIdLegs_idUnique (s : Multiset ExternalLeg) :
    ∀ ℓ₁ ∈ uniqueIdLegs s, ∀ ℓ₂ ∈ uniqueIdLegs s,
      ℓ₁.legId = ℓ₂.legId → ℓ₁ = ℓ₂ := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hid
  simp only [uniqueIdLegs, Multiset.mem_coe, List.mem_map] at hℓ₁ hℓ₂
  obtain ⟨p₁, hp₁, rfl⟩ := hℓ₁
  obtain ⟨p₂, hp₂, rfl⟩ := hℓ₂
  have hi : p₁.2 = p₂.2 := congrArg ResolvedLegId.id hid
  have g₁ := (List.mem_zipIdx_iff_getElem?).mp hp₁
  have g₂ := (List.mem_zipIdx_iff_getElem?).mp hp₂
  rw [hi, g₂] at g₁
  have : p₁.1 = p₂.1 := (Option.some.injEq _ _).mp g₁.symm
  simp only [this, hi]

/-- **Unique-id resolved lift of a flat graph.**  Same vertices; edges/legs tagged
by occurrence index.-/
noncomputable def ofFlatGraphWithUniqueIds (G : FeynmanGraph) : ResolvedFeynmanGraph :=
  { vertices := G.vertices
    internalEdges := uniqueIdEdges G.internalEdges
    externalLegs := uniqueIdLegs G.externalLegs }

@[simp] theorem ofFlatGraphWithUniqueIds_internalEdges (G : FeynmanGraph) :
    (ofFlatGraphWithUniqueIds G).internalEdges = uniqueIdEdges G.internalEdges := rfl
@[simp] theorem ofFlatGraphWithUniqueIds_externalLegs (G : FeynmanGraph) :
    (ofFlatGraphWithUniqueIds G).externalLegs = uniqueIdLegs G.externalLegs := rfl

/-- **forget round-trips on the unique-id lift.**-/
theorem forget_ofFlatGraphWithUniqueIds (G : FeynmanGraph) :
    (ofFlatGraphWithUniqueIds G).forget = G := by
  show ResolvedFeynmanGraph.forget _ = _
  unfold ResolvedFeynmanGraph.forget ofFlatGraphWithUniqueIds
  rw [map_forget_uniqueIdEdges, map_forget_uniqueIdLegs]

/-- **The unique-id lift has unique edge ids.**-/
theorem edgeIdsUnique_ofFlatGraphWithUniqueIds (G : FeynmanGraph) :
    (ofFlatGraphWithUniqueIds G).EdgeIdsUnique :=
  uniqueIdEdges_idUnique G.internalEdges

/-- **The unique-id lift has unique leg ids.**-/
theorem legIdsUnique_ofFlatGraphWithUniqueIds (G : FeynmanGraph) :
    (ofFlatGraphWithUniqueIds G).LegIdsUnique :=
  uniqueIdLegs_idUnique G.externalLegs

end GaugeGeometry.QFT.Combinatorial
