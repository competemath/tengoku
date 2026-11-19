import Tengoku.Linearhadwiger.HadwigerLean.Graph.CliqueDensity.Reduction
import Tengoku.Linearhadwiger.HadwigerLean.Graph.UnbalancedBipartite.BoundFinal
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The bipartite graph crossing two disjoint vertex sets
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private def crossValue (A B : Finset V) : (↥(A : Set V) ⊕ ↥(B : Set V)) → V
  | .inl a => a.1
  | .inr b => b.1

private theorem crossValue_injective (A B : Finset V) (hdisj : Disjoint A B) :
    Function.Injective (crossValue A B) := by
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr b =>
          have hab : a.1 = b.1 := hxy
          have haB : a.1 ∈ B := by rw [hab]; exact b.2
          exact False.elim ((Finset.disjoint_left.mp hdisj a.2) haB)
  | inr b =>
      cases y with
      | inl a =>
          have hba : b.1 = a.1 := hxy
          have hbA : b.1 ∈ A := by rw [hba]; exact a.2
          exact False.elim ((Finset.disjoint_left.mp hdisj hbA) b.2)
      | inr b' => exact congrArg Sum.inr (Subtype.ext hxy)

private def crossLeft (A B : Finset V) :
    Set (↥(A : Set V) ⊕ ↥(B : Set V)) :=
  {q | ∃ a, q = Sum.inl a}

private def crossRight (A B : Finset V) :
    Set (↥(A : Set V) ⊕ ↥(B : Set V)) :=
  {q | ∃ b, q = Sum.inr b}

private theorem crossLeft_disjoint_crossRight (A B : Finset V) :
    Disjoint (crossLeft A B) (crossRight A B) := by
  apply Set.disjoint_left.mpr
  intro q hqL hqR
  obtain ⟨a, rfl⟩ := hqL
  obtain ⟨b, hb⟩ := hqR
  cases hb

/-- All original edges between `A` and `B`, on a disjoint-sum vertex type.-/
noncomputable def crossGraph (G : SimpleGraph V) (A B : Finset V) :
    SimpleGraph (↥(A : Set V) ⊕ ↥(B : Set V)) :=
  (G.comap (crossValue A B)).between (crossLeft A B) (crossRight A B)

private noncomputable def crossLeftFinset (A B : Finset V) :
    Finset (↥(A : Set V) ⊕ ↥(B : Set V)) := by
  classical
  exact Finset.univ.filter (fun q => q ∈ crossLeft A B)

private noncomputable def crossRightFinset (A B : Finset V) :
    Finset (↥(A : Set V) ⊕ ↥(B : Set V)) := by
  classical
  exact Finset.univ.filter (fun q => q ∈ crossRight A B)

/--
@isnad1 id=isbipart.0h4v.s7.2dea588f15bf from=translated src=- shape=44e66648 vocab=ee9d9759
-/
theorem crossGraph_isBipartiteWith (G : SimpleGraph V) (A B : Finset V) :
    (crossGraph G A B).IsBipartiteWith
      (crossLeftFinset A B : Set _) (crossRightFinset A B : Set _) := by
  classical
  simpa [crossGraph, crossLeftFinset, crossRightFinset] using
    ((G.comap (crossValue A B)).between_isBipartiteWith
      (crossLeft_disjoint_crossRight A B))

/--
@isnad1 id=isminor.1h4v.s5.7d96eb77f1ff from=translated src=- shape=be99e886 vocab=5cc6e120
-/
theorem crossGraph_isMinor (G : SimpleGraph V)
    (A B : Finset V) (hdisj : Disjoint A B) :
    IsMinor (crossGraph G A B) G := by
  let H := G.comap (crossValue A B)
  have hle : crossGraph G A B ≤ H := SimpleGraph.between_le
  have hminorH : IsMinor H G := by
    let f : H →g G := {
      toFun := crossValue A B
      map_rel' := by intro x y hxy; exact hxy
    }
    exact ⟨(MinorModel.refl H).map f (crossValue_injective A B hdisj)⟩
  exact IsMinor.trans (isMinor_of_graph_le hle) hminorH

end HadwigerLean
