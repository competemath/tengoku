module

public import Tengoku.AtPalomar.Paper.Hyperbolic
public import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
public import Tengoku.Seed.Analysis.Normed.Group.Bounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Polynomial observables of tanh

Differentiating a polynomial in `tanh` preserves that class of observables.
Every such observable is uniformly bounded because `tanh` takes values in the
compact interval `[-1,1]`.
-/

open scoped Polynomial

namespace Paper

noncomputable def tanhPolynomialDeriv (P : ℝ[X]) : ℝ[X] :=
  P.derivative * (1 - Polynomial.X ^ 2)

/--
@isnad1 id=ex.0h1v.s5.0fbb1b3940ca from=translated src=- shape=f006f4cc vocab=6eb6cf31
-/
theorem exists_bound_tanhPolynomial (P : ℝ[X]) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, ‖P.eval (Real.tanh x)‖ ≤ M := by
  have hc : Continuous (fun y : ℝ => P.eval y) :=
    continuous_iff_continuousAt.mpr (fun x => (P.hasDerivAt x).continuousAt)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have hx : Real.tanh x ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp (Real.abs_tanh_lt_one x).le
  exact (hM _ hx).trans (le_max_left _ _)

/--
@isnad1 id=ex.0h1v.s5.0fbb1b3940ca from=translated src=- shape=f006f4cc vocab=6eb6cf31
-/
theorem tanhPolynomial_bounded (P : ℝ[X]) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, ‖P.eval (Real.tanh x)‖ ≤ M :=
  exists_bound_tanhPolynomial P

end Paper
