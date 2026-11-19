import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.ABSeparation
import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.DichotomyReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gluing a separator on the near shore across a critical separation

If Q separates original roots from the old boundary inside the near shore,
the whole far shore can be attached to the new far side. The glued boundary
has exactly |Q| vertices and retains the original far clique branch.
-/

namespace HadwigerLean

namespace VertexSeparation

/-- Glue a separation of the induced left shore to the original graph,
placing the original right shore on the new right side.-/
def glueLeft {V : Type*} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (G.induce S.left))
    (hX : ∀ x : S.left, (x : V) ∈ S.right → x ∈ T.right) :
    VertexSeparation G where
  left := {x | ∃ hx : x ∈ S.left, (⟨x, hx⟩ : S.left) ∈ T.left}
  right := {x | x ∈ S.right ∨ ∃ hx : x ∈ S.left,
    (⟨x, hx⟩ : S.left) ∈ T.right}
  cover := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hx : x ∈ S.left ∪ S.right := by
        rw [S.cover]
        trivial
      rcases hx with hxL | hxR
      · have ht : (⟨x, hxL⟩ : S.left) ∈ T.left ∪ T.right := by
          rw [T.cover]
          trivial
        rcases ht with htL | htR
        · exact Or.inl ⟨hxL, htL⟩
        · exact Or.inr (Or.inr ⟨hxL, htR⟩)
      · exact Or.inr (Or.inl hxR)
  no_cross := by
    intro x y hxL hxNR hyR hyNL hxy
    obtain ⟨hxSL, hxTL⟩ := hxL
    have hxTR : (⟨x, hxSL⟩ : S.left) ∉ T.right := by
      intro h
      exact hxNR (Or.inr ⟨hxSL, h⟩)
    have hxNotSR : x ∉ S.right := by
      intro h
      exact hxNR (Or.inl h)
    have crossT (hySL : y ∈ S.left)
        (hyTR : (⟨y, hySL⟩ : S.left) ∈ T.right) : False := by
      have hyNotTL : (⟨y, hySL⟩ : S.left) ∉ T.left := by
        intro h
        exact hyNL ⟨hySL, h⟩
      exact T.no_cross hxTL hxTR hyTR hyNotTL hxy
    rcases hyR with hySR | ⟨hySL, hyTR⟩
    · by_cases hySL : y ∈ S.left
      · exact crossT hySL (hX ⟨y, hySL⟩ hySR)
      · exact S.no_cross hxSL hxNotSR hySR hySL hxy
    · exact crossT hySL hyTR

/-- The original strict far shore remains strictly far after gluing.-/
theorem strictRight_glueLeft {V : Type*} [Fintype V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (T : VertexSeparation (G.induce S.left))
    (hX : ∀ x : S.left, (x : V) ∈ S.right → x ∈ T.right)
    {x : V} (hx : x ∈ S.strictRight) :
    x ∈ (S.glueLeft T hX).strictRight := by
  refine ⟨Or.inl hx.1, ?_⟩
  rintro ⟨hxL, _⟩
  exact hx.2 hxL

end VertexSeparation

end HadwigerLean
