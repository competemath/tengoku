import Tengoku.Seed.Analysis.Analytic.Basic
import Tengoku.Seed.Analysis.Normed.Operator.LinearIsometry
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Descent.CoefficientCriterion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof of Theorem 3.1

The two parts are `AlternatingAnalytic.CoefficientCriterion.diagonal_mem_range` and
`CoefficientCriterion.analyticAt_iff` (`Descent/CoefficientCriterion.lean`).
-/

namespace AlternatingAnalyticChallenge.Thm3_1

variable {K : Type*} [NontriviallyNormedField K]
  {P W Z : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z] [NormedSpace K Z]

/-- Every diagonal of an ambient expansion lies in `j(W)`.
@isnad1 id=mem.4h11v.s10.75ba5c748afe from=translated src=- shape=6de13acf vocab=22b2393c
-/
theorem part1 (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    (f : P → W) (x₀ : P) (b : FormalMultilinearSeries K P Z) (R : ℝ) (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    ∀ (n : ℕ) (h : P), b n (fun _ => h) ∈ Set.range j :=
  AlternatingAnalytic.CoefficientCriterion.diagonal_mem_range j hj f x₀ b R hR hbound hexp

/-- `f` is analytic at `x₀` if and only if the ambient diagonals have
`W`-valued bounded multilinear representatives with a positive common radius.
@isnad1 id=iff.4h9v.s10.bd2d3ccaa785 from=translated src=- shape=7315a419 vocab=7b236df8
-/
theorem part2 (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    (f : P → W) (x₀ : P) (b : FormalMultilinearSeries K P Z) (R : ℝ) (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    AnalyticAt K f x₀ ↔
      ∃ (q : FormalMultilinearSeries K P W) (r : ℝ), 0 < r ∧
        (∀ (n : ℕ) (h : P), j (q n (fun _ => h)) = b n (fun _ => h)) ∧
        BddAbove (Set.range fun n => ‖q n‖ * r ^ n) :=
  AlternatingAnalytic.CoefficientCriterion.analyticAt_iff j f x₀ b R hR hbound hexp

end AlternatingAnalyticChallenge.Thm3_1
