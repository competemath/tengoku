import Tengoku.OpenaiMath.OAI.Combinatorics.InfiniteMatroid.Ideals

namespace OAI

section

open Set Filter
open scoped symmDiff

namespace InfiniteMatroidCounterexample

namespace SubsetIdeal
variable {α : Type} (K : SubsetIdeal α) (U : Ultrafilter α)
  (hUK : ∀ N, K.small N → N ∉ U)

include hUK in
lemma large_of_modSubset {X Y : Set α} (hX : X ∈ U) (hXY : K.ModSubset X Y) : Y ∈ U := by
  have hc : (X \ Y)ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr (hUK _ hXY)
  exact Filter.mem_of_superset (inter_mem hX hc) (by intro x hx; by_contra hy; exact hx.2 ⟨hx.1, hy⟩)

include hUK in
lemma large_iff_symmDiff {X Y : Set α} (h : K.small (X ∆ Y)) : X ∈ U ↔ Y ∈ U := by
  exact ⟨fun hX ↦ K.large_of_modSubset U hUK hX (K.mono h (by simp [symmDiff_def])),
    fun hY ↦ K.large_of_modSubset U hUK hY (K.mono h (by simp [symmDiff_def]))⟩

end SubsetIdeal

/-- The properties of the ordinal rank which are used by the global assembly. -/
structure RankModel (α : Type) where
  ideal : SubsetIdeal α
  ultra : Ultrafilter α
  avoids : ∀ N, ideal.small N → N ∉ ultra
  rank : Set α → CIndex
  antitone : ∀ ⦃X Y⦄, X ∈ ultra → Y ∈ ultra → ideal.ModSubset X Y → rank Y ≤ rank X
  thinning : ∀ s X, s ⊆ X → s ∉ ultra → X ∈ ultra → ∀ γ : CIndex,
    ∃ u, s ⊆ u ∧ u ⊆ X ∧ u ∈ ultra ∧ γ < rank u

namespace RankModel
variable {α : Type} (R : RankModel α)
lemma invariant {X Y : Set α} (h : R.ideal.small (X ∆ Y)) :
    (X ∈ R.ultra ↔ Y ∈ R.ultra) ∧ (X ∈ R.ultra → R.rank X = R.rank Y) := by
  have he := R.ideal.large_iff_symmDiff R.ultra R.avoids h
  refine ⟨he, fun hX ↦ le_antisymm ?_ ?_⟩
  · exact R.antitone (he.mp hX) hX (R.ideal.mono h (by simp [symmDiff_def]))
  · exact R.antitone hX (he.mp hX) (R.ideal.mono h (by simp [symmDiff_def]))
end RankModel

section Construction
variable {α : Type}
variable (K : SubsetIdeal α) (G : CIndex → Set α) (U : Ultrafilter α)
  (hUK : ∀ N, K.small N → N ∉ U) (hG : ∀ t, G t ∈ U)
  (hfinite : ∀ X, X ∈ U → {t | K.ModSubset X (G t)}.Finite)

lemma exists_large_enumeration [Countable α] [Infinite α] : ∃ F : CIndex → Set α,
    (∀ i, F i ∈ U) ∧ ∀ X, X ∈ U → ∃ i, F i = X := by
  classical
  obtain ⟨e, he⟩ := exists_set_enumeration α
  refine ⟨fun i ↦ if e i ∈ U then e i else univ, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h
    · exact h
    · exact univ_mem
  · intro X hX
    obtain ⟨i, hi⟩ := he X
    exact ⟨i, by simp [hi, hX]⟩

variable (F : CIndex → Set α) (hF : ∀ i, F i ∈ U)
  (hFs : ∀ X, X ∈ U → ∃ i, F i = X)

include hFs in
lemma rank_candidates_nonempty {X : Set α} (hX : X ∈ U) :
    {i | K.ModSubset (F i) X}.Nonempty := by
  obtain ⟨i, rfl⟩ := hFs X hX
  exact ⟨i, K.modSubset_refl _⟩

noncomputable def ordinalRank (X : Set α) : CIndex := by
  classical
  exact if hX : X ∈ U then wellFounded_lt.min {i | K.ModSubset (F i) X}
    (rank_candidates_nonempty K U F hFs hX)
  else cindexBinaryEquiv.symm (fun _ ↦ false)

end Construction
end InfiniteMatroidCounterexample
end

end OAI
