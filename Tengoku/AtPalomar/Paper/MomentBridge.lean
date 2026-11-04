module

public import Tengoku.AtPalomar.Paper.Structural
public import Tengoku.AtPalomar.Paper.HeatContraction
public import Tengoku.AtPalomar.Paper.Variational

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Analytic Doob moments and the conditional right-hand bound

The moments in this file are literal Gaussian integrals of the proven positive,
normalized Gaussian Doob operator. Their initial values, moment comparison,
and exponential decay are proved. Transition-law identification with the
paper's diffusion and the Itô derivative identity remain explicit hypotheses.
This file does not assert Proposition 5.1 or identify an SDE solution.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- The Gaussian average of the actual Doob transform of squared `tanh`.-/
def gaussianDoobSecondMoment (β h q : ℝ) (lam : ℝ≥0) : ℝ :=
  ∫ x, doobOperator lam (fun y => Real.tanh y ^ 2) x
    ∂gaussianReal h (β ^ 2 * q).toNNReal

/-- The Gaussian average of the actual Doob transform of fourth-power `sech`.-/
def gaussianDoobFourthMoment (β h q : ℝ) (lam : ℝ≥0) : ℝ :=
  ∫ x, doobOperator lam (fun y => sech y ^ 4) x
    ∂gaussianReal h (β ^ 2 * q).toNNReal

/-- The actual analytic second moment at time `t`, with time rescaling by `β²`.
The nonnegative-real truncation is inactive whenever `t ≥ q`.-/
def hardSecondMoment (β h q t : ℝ) : ℝ :=
  gaussianDoobSecondMoment β h q (β ^ 2 * (t - q)).toNNReal

/-- The actual analytic fourth-sech moment at time `t`.-/
def hardFourthMoment (β h q t : ℝ) : ℝ :=
  gaussianDoobFourthMoment β h q (β ^ 2 * (t - q)).toNNReal

/-- Bounded measurable Doob tests remain integrable under every Gaussian
initial law, so none of the analytic moment integrals is a junk integral.
@isnad1 id=integrab.2h4v.s5.66f7fb9e67de from=translated src=- shape=172bb05e vocab=a71515c5
-/
lemma integrable_gaussian_doob_bounded (h : ℝ) (v lam : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : Measurable ψ) (hbound : ∀ y, ‖ψ y‖ ≤ 1) :
    Integrable (doobOperator lam ψ) (gaussianReal h v) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (measurable_doobOperator lam ψ hψ).aestronglyMeasurable
  · filter_upwards [] with x
    exact norm_doobOperator_le lam ψ hψ 1 hbound x

/-- Positivity of the operator yields positivity of the fourth moment.
@isnad1 id=le.0h4v.s4.4b46fa0074d5 from=translated src=- shape=b9ff034a vocab=f81f78a7
-/
theorem gaussianDoobFourthMoment_nonneg (β h q : ℝ) (lam : ℝ≥0) :
    0 ≤ gaussianDoobFourthMoment β h q lam := by
  exact integral_nonneg (fun x => doobOperator_nonneg lam _
    (fun y => (pow_nonneg (sech_pos y).le 4)) x)

/--
@isnad1 id=le.0h4v.s4.8800bdb5809d from=translated src=- shape=b9ff034a vocab=de323d93
-/
theorem gaussianDoobSecondMoment_nonneg (β h q : ℝ) (lam : ℝ≥0) :
    0 ≤ gaussianDoobSecondMoment β h q lam := by
  exact integral_nonneg (fun x => doobOperator_nonneg lam _ (fun y => sq_nonneg _) x)

end Paper
