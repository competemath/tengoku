import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.StageDeletion
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Remove the old model's unique tangency vertices

The first move of a nonzero inseparability stage deletes exactly one vertex
per old branch from the highly connected region. The residual is disjoint
from the entire old model.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

def StageState.tangentFinset
    (S : StageState G s k m coreBound) : Finset V :=
  Finset.univ.image S.root

/--
@isnad1 id=eq.0h7v.s5.9041b5b1bd6f from=translated src=- shape=9e9efcef vocab=64eb186e
-/
theorem StageState.tangentFinset_card
    (S : StageState G s k m coreBound) :
    S.tangentFinset.card = s := by
  classical
  simp [StageState.tangentFinset,
    Finset.card_image_of_injective _ S.root_injective]

/--
@isnad1 id=le.1h7v.s6.924b0dc2a44d from=translated src=- shape=dafc747f vocab=48848255
-/
theorem StageState.tangentFinset_subset_region
    (S : StageState G s k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region) :
    S.tangentFinset ⊆ S.region := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  exact hrootregion i

/--
@isnad1 id=disjoint.1h7v.s7.041ee2237967 from=translated src=- shape=9f96c5ed vocab=094b945f
-/
theorem StageState.model_disjoint_region_without_tangencies
    (S : StageState G s k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region) :
    Disjoint S.model.toMinorModel.vertices
      ((S.region \ S.tangentFinset : Finset V) : Set V) := by
  classical
  apply Set.disjoint_left.mpr
  intro v hvM hvR
  obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hvM
  have hvRegion : v ∈ S.region := (Finset.mem_sdiff.mp hvR).1
  obtain ⟨w, _, huniq⟩ := S.tangent i
  have hvEq : v = w := huniq v ⟨hvi,hvRegion⟩
  have hrEq : S.root i = w :=
    huniq (S.root i) ⟨S.model.root_mem i,hrootregion i⟩
  have hvD : v ∈ S.tangentFinset := by
    rw [hvEq, ← hrEq]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  exact (Finset.mem_sdiff.mp hvR).2 hvD

/-- The exact deletion package used before selecting the small connected
pieces for the next stage.
@isnad1 id=and.2h8v.s8.fa779be64914 from=translated src=- shape=00f4538d vocab=eac58ce1
-/
theorem StageState.after_remove_tangencies
    (S : StageState G s k m coreBound)
    (hrootregion : ∀ i, S.root i ∈ S.region)
    (ℓ : ℕ) (hbudget : s + ℓ ≤ k) :
    VertexConnected
      (G.induce ((S.region \ S.tangentFinset : Finset V) : Set V)) ℓ ∧
    chromatic G ≤
      chromatic (G.induce
        ((S.region \ S.tangentFinset : Finset V) : Set V)) + m + s ∧
    Disjoint S.model.toMinorModel.vertices
      ((S.region \ S.tangentFinset : Finset V) : Set V) := by
  classical
  have hD := S.after_delete S.tangentFinset
    (S.tangentFinset_subset_region hrootregion) ℓ
    (by rw [S.tangentFinset_card]; exact hbudget)
  refine ⟨hD.1, ?_, S.model_disjoint_region_without_tangencies hrootregion⟩
  rw [S.tangentFinset_card] at hD
  exact hD.2

end Inseparability
end HadwigerLean
