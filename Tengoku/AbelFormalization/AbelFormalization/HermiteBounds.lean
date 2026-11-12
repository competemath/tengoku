import Tengoku.AbelFormalization.AbelFormalization.HermiteKernel
import Tengoku.AbelFormalization.AbelFormalization.HermiteNodeBounds
import Tengoku.Seed.Analysis.Normed.Group.Bounded
import Tengoku.Seed.Analysis.Normed.Group.Constructions
import Tengoku.Seed.Topology.MetricSpace.ProperSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform bounds for Hermite coefficient kernels

Each coefficient of the node polynomial and of the divided-difference kernel
is continuous jointly in the nodes and the contour point. On the closed node
polydisk and the contour circle, the denominator is bounded away from zero.
Compactness then supplies one positive bound for every coefficient below the
total multiplicity, including when nodes coincide.
-/

noncomputable section

namespace AbelFormalization

open Polynomial Set Metric

variable {ι : Type*} [Fintype ι]

/-- Joint continuity of evaluating the node polynomial at the contour point.-/
theorem continuous_nodePolynomial_eval_joint (m : ι → ℕ) :
    Continuous (fun p : (ι → ℂ) × ℂ => (nodePolynomial p.1 m).eval p.2) := by
  simp only [nodePolynomial_eval]
  exact continuous_finsetProd _ fun i _ =>
    (continuous_snd.sub ((continuous_apply i).comp continuous_fst)).pow (m i)

/-- The scalar coefficient kernel in contour Hermite interpolation.-/
def hermiteCoefficientKernel (δ : ι → ℂ) (m : ι → ℕ) (ζ : ℂ) (j : ℕ) : ℂ :=
  (hermiteKernel (nodePolynomial δ m) ζ).coeff j / (nodePolynomial δ m).eval ζ

/-- The closed parameter domain used to obtain a uniform coefficient bound.-/
def hermiteContourParameters (B : ℝ) : Set ((ι → ℂ) × ℂ) :=
  {p | (∀ i, ‖p.1 i‖ ≤ B + 1 / 4) ∧ ‖p.2‖ = B + 1}

omit [Fintype ι] in
theorem isCompact_hermiteContourParameters (B : ℝ) :
    IsCompact (hermiteContourParameters (ι := ι) B) := by
  have hn : IsCompact {δ : ι → ℂ | ∀ i, δ i ∈ closedBall 0 (B + 1 / 4)} :=
    isCompact_pi_infinite fun _ => isCompact_closedBall 0 (B + 1 / 4)
  have hn' : IsCompact {δ : ι → ℂ | ∀ i, ‖δ i‖ ≤ B + 1 / 4} := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  have hs : IsCompact {ζ : ℂ | ‖ζ‖ = B + 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : ℂ) (B + 1)
  exact hn'.prod hs

end AbelFormalization
