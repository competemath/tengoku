import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.RawModelAdjacency
import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.RawModelCI
import Tengoku.Linearhadwiger.HadwigerLean.Woven.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Avoidance of D and H3 by the old and child model pieces

Every supplementary branch piece belongs to either the old model or
one of the child models. A set avoided by all of those models is avoided
by every piece passed to the raw model assembly.
-/

namespace HadwigerLean.Inseparability

universe u

/--
@isnad1 id=le.0h8v.s6.dcdd3222084f from=translated src=- shape=49ca4490 vocab=6730a0d1
-/
theorem ciExtraPiece_subset_model_union
    {V : Type u} (p x : ℕ) {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (z : CIRawIndex p x) (j : Option (Fin p)) :
    ciExtraPiece p x A M z j ⊆
      A.vertices ∪ ⋃ i, (M i).vertices := by
  cases z with
  | inl z =>
      obtain ⟨i,r⟩ := z
      cases j with
      | none =>
          intro v hv
          exact Or.inl (Set.mem_iUnion.mpr ⟨(i,r),hv⟩)
      | some k =>
          by_cases hki : k = i
          · subst k
            intro v hv
            exact Or.inr (Set.mem_iUnion.mpr
              ⟨i,Set.mem_iUnion.mpr ⟨(0,r),by simpa [ciExtraPiece] using hv⟩⟩)
          · simp [ciExtraPiece, hki]
  | inr r =>
      cases j with
      | none => simp [ciExtraPiece]
      | some i =>
          intro v hv
          exact Or.inr (Set.mem_iUnion.mpr
            ⟨i,Set.mem_iUnion.mpr ⟨(1,r),hv⟩⟩)

/--
@isnad1 id=disjoint.2h9v.s7.1d5f9913e19e from=translated src=- shape=60c101d8 vocab=40919240
-/
theorem ciExtraPiece_disjoint_of_models
    {V : Type u} (p x : ℕ) {G : SimpleGraph V}
    (A : MinorModel (SimpleGraph.completeGraph (Fin p × Fin x)) G)
    (M : Fin p → MinorModel
      (SimpleGraph.completeGraph (Fin 2 × Fin x)) G)
    (T : Set V)
    (hAT : Disjoint A.vertices T)
    (hMT : ∀ i, Disjoint (M i).vertices T) :
    ∀ z j, Disjoint (ciExtraPiece p x A M z j) T := by
  intro z j
  apply Set.disjoint_left.mpr
  intro v hvT hv
  rcases ciExtraPiece_subset_model_union p x A M z j hvT with
    hvA | hvM
  · exact (Set.disjoint_left.mp hAT) hvA hv
  · obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hvM
    exact (Set.disjoint_left.mp (hMT i)) hvi hv

end HadwigerLean.Inseparability
