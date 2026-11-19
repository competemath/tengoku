import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.PackedMax
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The block vertices in a simultaneous contraction quotient
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

noncomputable def ConnectedBlockFamily.blockVertices : Finset F.Vertex := by
  classical
  exact Finset.univ.filter fun q =>
    match q with | .inl _ => True | .inr _ => False

/--
@isnad1 id=mem.0h4v.s7.da9360c03475 from=translated src=- shape=b964feab vocab=70e9243d
-/
theorem ConnectedBlockFamily.mem_blockVertices_inl
    (B : ↥(F.blocks : Set (Finset V))) :
    (Sum.inl B : F.Vertex) ∈ F.blockVertices := by
  simp [ConnectedBlockFamily.blockVertices]

/--
@isnad1 id=not.0h4v.s7.8ee110b71785 from=translated src=- shape=ba609bee vocab=d1661494
-/
theorem ConnectedBlockFamily.not_mem_blockVertices_inr
    (x : {v : V // v ∉ F.covered}) :
    (Sum.inr x : F.Vertex) ∉ F.blockVertices := by
  simp [ConnectedBlockFamily.blockVertices]

/--
@isnad1 id=eq.0h3v.s5.d26fd775617e from=translated src=- shape=680e9e1c vocab=504b9de4
-/
theorem ConnectedBlockFamily.blockVertices_card :
    F.blockVertices.card = F.blocks.card := by
  classical
  have heq : F.blockVertices =
      (Finset.univ : Finset ↥(F.blocks : Set (Finset V))).map
        Function.Embedding.inl := by
    ext q
    cases q <;> simp [ConnectedBlockFamily.blockVertices]
  rw [heq, Finset.card_map]
  simpa using Fintype.card_coe F.blocks

/--
@isnad1 id=disjoint.0h4v.s5.4d321df4b11d from=translated src=- shape=105adfee vocab=68f21691
-/
theorem ConnectedBlockFamily.singletonLift_disjoint_blockVertices
    (H : Finset V) : Disjoint (F.singletonLift H) F.blockVertices := by
  apply Finset.disjoint_left.mpr
  intro q hq hblock
  cases q with
  | inl B => exact F.not_mem_singletonLift_inl H B hq
  | inr x => exact F.not_mem_blockVertices_inr x hblock

end HadwigerLean
