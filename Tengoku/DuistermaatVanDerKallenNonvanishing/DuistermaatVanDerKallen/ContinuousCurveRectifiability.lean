import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicCurveRegularity
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CurveRectifiability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform integrated-speed and metric-length bounds for bounded continuous
Euclidean curve families with semialgebraic coordinate graphs. Regularity
outside finitely many points is derived for each curve. Full graph fiber
counts bound variation uniformly without a uniform exceptional-point count.
This constructs neither the curves nor a Hardt trivialization. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory

theorem semialgebraic_curve_family_individual_graph
    {ι κ : Type*} [Fintype κ] (γ : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (a : ι → ℝ) (i : κ) :
    IsSemialgebraic (Unit ⊕ Unit) {q | q (.inl ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ a (q (.inl ())) i = q (.inr ())} := by
  let p : ((ι ⊕ Unit) ⊕ Unit) → MvPolynomial (Unit ⊕ Unit) ℝ :=
    Sum.elim (Sum.elim (fun j => MvPolynomial.C (a j))
      (fun _ => MvPolynomial.X (.inr ()))) (fun _ => MvPolynomial.X (.inl ()))
  simpa [p] using (hgraph i).polynomial_preimage p

end
end DuistermaatVanDerKallen
