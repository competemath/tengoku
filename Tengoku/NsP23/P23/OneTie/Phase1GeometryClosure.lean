import Tengoku.NsP23.P23.OneTie.GeometryClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stable Phase-1 geometry API

Future work may import this module and use the two geometry conclusions without
opening the H5 classification or its internal elimination lemmas.
-/

namespace P23.OneTie

structure PhaseOneFourBorderGeometry : Prop where
  mixed : ∀ (a b c : ℕ) [NeZero a] (S : Finset (Normal a b c)),
    2 ≤ a → 1 ≤ b → 1 ≤ c → S.card = 3 → IsLiveTie S →
    IsRootAntichain S → HasDirectionalCentres S →
    (borderFinset S).card = 4 → ∃ C ∈ S, IsDominantRoot S C
  pure : ∀ (a b : ℕ) [NeZero a] (S : Finset (Normal a b 0)),
    2 ≤ a → 2 ≤ b → S.card = 3 → IsLiveTie S →
    IsRootAntichain S → HasDirectionalCentres S →
    (borderFinset S).card = 4 →
      (∃ C ∈ S, IsDominantRoot S C) ∨ IsPureResidualFourBorderShape S

/-- The Run-06 Phase-1 closure milestone, exposing only the mixed and pure
four-border conclusions needed by later work.
@isnad1 id=phaseone.0h0v.s0.d8f675ddbfed from=translated src=- shape=45709ebd vocab=d8f675dd
-/
theorem phaseOne_four_border_geometry : PhaseOneFourBorderGeometry where
  mixed := by
    intro a b c _ S ha hb hc hcard hlive hanti hcentres hborder
    exact mixed_four_border_has_dominant S ha hb hc hcard hlive hanti
      hcentres hborder
  pure := by
    intro a b _ S ha hb hcard hlive hanti hcentres hborder
    exact pure_four_border_dominant_or_residual S ha hb hcard hlive hanti
      hcentres hborder

end P23.OneTie
