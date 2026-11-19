import Tengoku.Linearhadwiger.HadwigerLean.Quantitative.RobustBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional final assembly for Theorem 2

This module isolates the exact final statement from the two outstanding
combinatorial inputs. Its assumptions are explicit theorems to be supplied
by the low-codegree rounding and robust fractional-coloring developments.
-/

namespace HadwigerLean.Theorem2

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The paper's quantitative bound follows from the low-codegree rounding
inequality and the robust fractional bound. Both inputs are quantified over
all finite graphs so that they apply to induced residual graphs.
@isnad1 id=le.4h3v.s8.65af3a764689 from=translated src=- shape=65887faf vocab=f71982ba
-/
theorem quantitative_bound_of_rounding_and_robust
    (G : SimpleGraph V)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hround : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W),
      independenceNumber H ≤ m ε →
      n0 ε ≤ Fintype.card W →
      ∀ x : StableSet H → ℝ,
        IsPairConstrainedColoring H (mu ε / 4) x →
        (∀ v, vertexLoad H x v = 1) →
        (chromatic H : ℝ) ≤ fractionalCost H x +
          gamma ε * (Fintype.card W : ℝ))
    (hrobust : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (F : SimpleGraph W),
      independenceNumber H ≤ m ε →
      F ≤ Hᶜ →
      (letI : DecidableRel F.Adj := Classical.decRel F.Adj
       F.maxDegree) ≤ d ε →
      fractionalChromaticNumber (H ⊔ F) ≤
        4 * (cliqueMinorNumber H : ℝ) +
          (robustAdditive ε : ℝ)) :
    (chromatic G : ℝ) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        ε * (Fintype.card V : ℝ) + Aepsilon ε := by
  classical
  apply quantitative_bound_of_bounded_induced_A G ε hε hε1 ?_ (A_le_Aepsilon hε hε1)
  intro J hα
  have hJ := bounded_independence_from_rounding_and_robust
    (G.induce (J : Set V)) ε hε hε1 hα
    (hround (J : Set V) (G.induce (J : Set V)) hα)
    (fun F => hrobust (J : Set V) (G.induce (J : Set V)) F hα)
  have hcard : Fintype.card (J : Set V) = J.card := by
    exact Fintype.card_coe J
  simpa only [hcard] using hJ

/-- The robust fractional bound is now unconditional; the remaining input is
the low-codegree rounding inequality.
@isnad1 id=le.3h3v.s7.852e64f2c2d3 from=translated src=- shape=e6ada4e4 vocab=5bb1e332
-/
theorem quantitative_bound_of_rounding
    (G : SimpleGraph V)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hround : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W),
      independenceNumber H ≤ m ε →
      n0 ε ≤ Fintype.card W →
      ∀ x : StableSet H → ℝ,
        IsPairConstrainedColoring H (mu ε / 4) x →
        (∀ v, vertexLoad H x v = 1) →
        (chromatic H : ℝ) ≤ fractionalCost H x +
          gamma ε * (Fintype.card W : ℝ)) :
    (chromatic G : ℝ) ≤
      4 * (cliqueMinorNumber G : ℝ) +
        ε * (Fintype.card V : ℝ) + Aepsilon ε := by
  exact quantitative_bound_of_rounding_and_robust G ε hε hε1 hround
    (robust_fractional_bound_at_theorem2_parameters ε hε hε1)
end HadwigerLean.Theorem2
