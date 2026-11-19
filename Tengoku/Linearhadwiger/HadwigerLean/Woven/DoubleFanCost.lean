import Tengoku.Linearhadwiger.HadwigerLean.Woven.DoubleFanChordless
import Tengoku.Linearhadwiger.HadwigerLean.Woven.DoubleFanColor
import Tengoku.Linearhadwiger.HadwigerLean.Graph.VertexConnectivity
import Tengoku.Linearhadwiger.HadwigerLean.Graph.ChromaticSlice
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Double fans with a controlled chromatic footprint
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V}

/-- On an induced graph, coloring one chosen set with a private palette
costs its chromatic number in the ambient graph.-/
theorem chromatic_induce_le_add_remainder
    (G : SimpleGraph V) (S A : Set V) :
    chromatic (G.induce S) ≤
      chromatic (G.induce A) + chromatic (G.induce (S \ A)) := by
  classical
  let m := chromatic (G.induce A)
  let n := chromatic (G.induce (S \ A))
  let cA : (G.induce A).Coloring (Fin m) :=
    Classical.choice (colorable_chromatic _)
  let cR : (G.induce (S \ A)).Coloring (Fin n) :=
    Classical.choice (colorable_chromatic _)
  let c : (G.induce S).Coloring (Fin m ⊕ Fin n) :=
    SimpleGraph.Coloring.mk
      (fun x => if hx : x.1 ∈ A then Sum.inl (cA ⟨x.1,hx⟩)
        else Sum.inr (cR ⟨x.1, ⟨x.2,hx⟩⟩))
      (by
        intro x y hxy
        dsimp
        split_ifs with hx hy
        · exact Sum.inl_injective.ne (cA.valid hxy)
        · intro h
          cases h
        · intro h
          cases h
        · exact Sum.inr_injective.ne (cR.valid hxy))
  have hc : (G.induce S).Colorable (m + n) := by
    simpa [Fintype.card_sum] using c.colorable
  exact (chromatic_le_iff_colorable _ _).mpr hc

/-- A double fan, its sources, and a hub can be removed with their exact
separate palette costs.-/
theorem DoubleFan.chromatic_le_source_hub_fan_residual
    (F : DoubleFan G Z H) (hfan :
      chromatic (G.induce (F.vertexFinset : Set V)) ≤ 4 * Z.card) :
    chromatic G ≤ Z.card + chromatic (G.induce (H : Set V)) +
      4 * Z.card +
      chromatic (G.induce ((Z ∪ H ∪ F.vertexFinset : Finset V) : Set V)ᶜ) := by
  classical
  have hZ : chromatic (G.induce (Z : Set V)) ≤ Z.card := by
    simpa using chromatic_le_card (G.induce (Z : Set V))
  have h₁ := chromatic_induce_le_add_remainder G Set.univ (Z : Set V)
  have h₂ := chromatic_induce_le_add_remainder G (Z : Set V)ᶜ (H : Set V)
  have h₃ := chromatic_induce_le_add_remainder G
    (((Z : Set V) ∪ (H : Set V))ᶜ) (F.vertexFinset : Set V)
  have huniv : chromatic (G.induce Set.univ) = chromatic G := by
    have hu : ((Finset.univ : Finset V) : Set V) = Set.univ := by
      ext x
      simp
    rw [← hu]
    exact chromatic_induce_univ_finset G
  rw [huniv] at h₁
  have hset₁ : Set.univ \ (Z : Set V) = (Z : Set V)ᶜ := by
    ext x
    simp
  have h₁' : chromatic G ≤
      chromatic (G.induce (Z : Set V)) + chromatic (G.induce (Z : Set V)ᶜ) := by
    rw [hset₁] at h₁
    exact h₁
  have hset₂ : (Z : Set V)ᶜ \ (H : Set V) =
      (((Z : Set V) ∪ (H : Set V))ᶜ) := by
    ext x
    simp [not_or]
  have h₂' : chromatic (G.induce (Z : Set V)ᶜ) ≤
      chromatic (G.induce (H : Set V)) +
        chromatic (G.induce (((Z : Set V) ∪ (H : Set V))ᶜ)) := by
    rw [hset₂] at h₂
    exact h₂
  have hset₃ : (((Z : Set V) ∪ (H : Set V))ᶜ) \ (F.vertexFinset : Set V) =
      ((Z ∪ H ∪ F.vertexFinset : Finset V) : Set V)ᶜ := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_union,
      Finset.mem_coe, Finset.mem_union]
    tauto
  have h₃' : chromatic (G.induce (((Z : Set V) ∪ (H : Set V))ᶜ)) ≤
      chromatic (G.induce (F.vertexFinset : Set V)) +
        chromatic (G.induce ((Z ∪ H ∪ F.vertexFinset : Finset V) : Set V)ᶜ) := by
    rw [hset₃] at h₃
    exact h₃
  omega
end Woven
end HadwigerLean
