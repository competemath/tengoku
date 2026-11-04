import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicBoundary
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.BivariatePolynomials
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AlgebraicCurveRegularity
import Tengoku.Seed.Analysis.InnerProductSpace.Calculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuous semialgebraic curves are smooth outside finitely many interior
parameter values. The exceptional set is constructed from the graph, not
assumed. Uniform family bounds and endpoint reparametrizations are not
asserted by these individual-curve results. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

theorem semialgebraic_scalar_polynomial_relation
    (f : ℝ → ℝ) (S : Set ℝ)
    (hgraph : IsSemialgebraic (Unit ⊕ Unit) {q | q (.inl ()) ∈ S ∧
      f (q (.inl ())) = q (.inr ())}) :
    ∃ P : Polynomial (Polynomial ℝ), P ≠ 0 ∧
      ∀ x ∈ S, bivariateEval P (x, f x) = 0 := by
  obtain ⟨p, hp, hroot⟩ := semialgebraic_scalar_graph_polynomial
    (fun x : Unit → ℝ => f (x ())) {x | x () ∈ S} hgraph
  refine ⟨bivariatePolynomialEquiv p, ?_, ?_⟩
  · exact (map_ne_zero_iff bivariatePolynomialEquiv bivariatePolynomialEquiv.injective).mpr hp
  · intro x hx
    rw [bivariateEval, eval_bivariatePolynomialEquiv]
    exact hroot (fun _ => x) hx

end
end DuistermaatVanDerKallen
