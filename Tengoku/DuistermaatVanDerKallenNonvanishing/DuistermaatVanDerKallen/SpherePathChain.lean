import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SpherePathEstimate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite pieces of continuously differentiable paths, with length measured by
integrating their speeds. No regularity at the junctions is asserted. -/

namespace DuistermaatVanDerKallen
noncomputable section

/-- Only indices below `pieces` describe arcs; the remaining entries are ignored.-/
structure C1ArcChain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (x y : E) where
  pieces : ℕ
  node : ℕ → E
  curve : ℕ → ℝ → E
  velocity : ℕ → ℝ → E
  source : node 0 = x
  target : node pieces = y
  node_mem : ∀ i, i ≤ pieces → node i ∈ S
  start : ∀ i, i < pieces → curve i 0 = node i
  finish : ∀ i, i < pieces → curve i 1 = node (i + 1)
  derivative : ∀ i, i < pieces → ∀ t ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt (curve i) (velocity i t) (Set.Icc 0 1) t
  velocity_continuous : ∀ i, i < pieces → ContinuousOn (velocity i) (Set.Icc (0 : ℝ) 1)
  curve_mem : ∀ i, i < pieces → ∀ t ∈ Set.Icc (0 : ℝ) 1, curve i t ∈ S

namespace C1ArcChain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {x y : E}

def length (γ : C1ArcChain S x y) : ℝ :=
  ∑ i ∈ Finset.range γ.pieces, ∫ t in (0 : ℝ)..1, ‖γ.velocity i t‖

/--
@isnad1 id=le.0h5v.s5.0c248aa8b658 from=translated src=- shape=5fe4e7a6 vocab=2fb4ba3d
-/
theorem length_nonneg (γ : C1ArcChain S x y) : 0 ≤ γ.length := by
  apply Finset.sum_nonneg
  intro i hi
  exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)

end C1ArcChain

/-- OPEN: the manuscript path input expressed by finite C1 pieces and their
integrated lengths. Uniformity is in both radius and threshold. This is not
inferred from the earlier, weaker rectifiable-path obligation.-/
def SphereC1ChainObligation : Prop :=
  ∀ d (g : Fin d → AmbientPolynomial d),
    ∃ N : ℕ, 1 ≤ N ∧ ∃ L : ℝ, 1 ≤ L ∧
    ∀ R ε : ℝ, 1 < R → 0 < ε →
    ∃ label : smallGradientSphere g R ε → Fin N,
      (∀ x y, label x = label y ↔
        y.val ∈ connectedComponentIn (smallGradientSphere g R ε) x.val) ∧
      ∀ x y : smallGradientSphere g R ε, label x = label y →
        ∃ γ : C1ArcChain (smallGradientSphere g R ε) x.val y.val, γ.length ≤ L

end
end DuistermaatVanDerKallen
