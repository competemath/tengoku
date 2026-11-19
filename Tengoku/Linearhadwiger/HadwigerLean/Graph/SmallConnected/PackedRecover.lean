import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.PackedVertices
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Recovering original vertices from an uncovered quotient set
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

noncomputable def ConnectedBlockFamily.originalOfSingletons
    (U : Finset F.Vertex) : Finset V :=
  U.biUnion fun q =>
    match q with
    | .inl _ => ∅
    | .inr x => {x.1}

/--
@isnad1 id=iff.0h5v.s7.ab1d1a745cb1 from=translated src=- shape=4a0008d3 vocab=70ca4f99
-/
theorem ConnectedBlockFamily.mem_originalOfSingletons
    (U : Finset F.Vertex) (v : V) :
    v ∈ F.originalOfSingletons U ↔
      ∃ x : {v : V // v ∉ F.covered}, Sum.inr x ∈ U ∧ x.1 = v := by
  simp only [ConnectedBlockFamily.originalOfSingletons,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hv⟩
    cases q with
    | inl B => simp at hv
    | inr x =>
        have hval : v = x.1 := by simpa using hv
        exact ⟨x, hq, hval.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨.inr x, hx, by simp⟩

/--
@isnad1 id=disjoint.0h4v.s5.5bc5a00bf9bd from=translated src=- shape=2f6129aa vocab=b503ce34
-/
theorem ConnectedBlockFamily.originalOfSingletons_disjoint_covered
    (U : Finset F.Vertex) :
    Disjoint (F.originalOfSingletons U) F.covered := by
  apply Finset.disjoint_left.mpr
  intro v hv hcov
  obtain ⟨x, _, rfl⟩ := (F.mem_originalOfSingletons U v).mp hv
  exact x.2 hcov

/--
@isnad1 id=eq.1h4v.s6.dc4de3ed1790 from=translated src=- shape=b6c8d99d vocab=219a614b
-/
theorem ConnectedBlockFamily.singletonLift_originalOfSingletons
    (U : Finset F.Vertex) (hU : Disjoint U F.blockVertices) :
    F.singletonLift (F.originalOfSingletons U) = U := by
  ext q
  cases q with
  | inl B =>
      have hnotU : (Sum.inl B : F.Vertex) ∉ U := by
        intro hB
        exact (Finset.disjoint_left.mp hU hB)
          (F.mem_blockVertices_inl B)
      simp [F.not_mem_singletonLift_inl, hnotU]
  | inr x =>
      rw [F.mem_singletonLift_inr,
        F.mem_originalOfSingletons]
      constructor
      · rintro ⟨y, hy, hval⟩
        have hxy : x = y := Subtype.ext hval.symm
        simpa [hxy] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩

/--
@isnad1 id=eq.1h4v.s6.3c2b6b367b93 from=translated src=- shape=ad313a87 vocab=688e0c64
-/
theorem ConnectedBlockFamily.originalOfSingletons_card
    (U : Finset F.Vertex) (hU : Disjoint U F.blockVertices) :
    (F.originalOfSingletons U).card = U.card := by
  have h := F.singletonLift_card (F.originalOfSingletons U)
    (F.originalOfSingletons_disjoint_covered U)
  rw [F.singletonLift_originalOfSingletons U hU] at h
  exact h.symm

/--
@isnad1 id=connecte.2h4v.s7.69e31161906d from=translated src=- shape=9a5782ee vocab=a06230fa
-/
theorem ConnectedBlockFamily.originalOfSingletons_connected
    (U : Finset F.Vertex) (hU : Disjoint U F.blockVertices)
    (hconn : (F.quotient.induce (U : Set F.Vertex)).Connected) :
    (G.induce (F.originalOfSingletons U : Set V)).Connected := by
  have h := (F.singletonLiftIso (F.originalOfSingletons U)
    (F.originalOfSingletons_disjoint_covered U)).connected_iff
  rw [F.singletonLift_originalOfSingletons U hU] at h
  exact h.mpr hconn

end HadwigerLean
