import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.StageChildReindex
import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.RawModelCI
import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.RawModelAttachment
import Tengoku.Linearhadwiger.HadwigerLean.Woven.ManyChildRerouting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# CI child rerouting with two-sided branch labels

Apply the finite sequential woven rerouting theorem to all p small
pieces, then convert each rooted K_(2x) model to the side-and-offset
branch labels required by the raw CI model.
-/

namespace HadwigerLean.Inseparability

universe u

theorem ciChildRootFin_terminal_of_starts
    {V : Type*} (p x : ℕ)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (P : IndexedPairs (CIPathIndex p x) V)
    (hOld : ∀ i r,
      P.start (ciOldMiddleIndex p x i r) = childRoot i (0,r))
    (hNew : ∀ i r,
      P.start (ciNewMiddleIndex p x i r) = childRoot i (1,r)) :
    ∀ i, Set.range (ciChildRootFin x (childRoot i)) ⊆ P.allTerminals := by
  intro i v hv
  obtain ⟨n,rfl⟩ := hv
  let z : Fin 2 × Fin x := finProdFinEquiv.symm n
  change childRoot i z ∈ P.allTerminals
  obtain ⟨d,r⟩ := z
  have hd : d = 0 ∨ d = 1 := by
    by_cases h : d.val = 0
    · exact Or.inl (Fin.ext h)
    · right
      apply Fin.ext
      have hdlt := d.isLt
      omega
  rcases hd with rfl | rfl
  · rw [← hOld i r]
    exact Set.mem_iUnion.mpr
      ⟨ciOldMiddleIndex p x i r, by simp [IndexedPairs.terminals]⟩
  · rw [← hNew i r]
    exact Set.mem_iUnion.mpr
      ⟨ciNewMiddleIndex p x i r, by simp [IndexedPairs.terminals]⟩

end HadwigerLean.Inseparability
