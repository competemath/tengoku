import Tengoku.AbelFormalization.AbelFormalization.HermiteBounds
import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic
import Tengoku.Seed.Analysis.Calculus.FDeriv.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic dependence of the Hermite coefficient kernels

The coefficients of the node polynomial are polynomial expressions in the nodes.
The contour coefficient kernels are therefore jointly analytic wherever their
denominator is nonzero, including when some nodes coincide.
-/

noncomputable section

namespace AbelFormalization

open Polynomial Set Metric

private theorem analyticAt_polynomial_coeff_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : E → ℂ[X]} {x : E}
    (hP : ∀ j, AnalyticAt ℂ (fun y => (P y).coeff j) x)
    (hQ : ∀ j, AnalyticAt ℂ (fun y => (Q y).coeff j) x) (j : ℕ) :
    AnalyticAt ℂ (fun y => (P y * Q y).coeff j) x := by
  simp only [Polynomial.coeff_mul]
  exact Finset.analyticAt_fun_sum _ fun ij _ => (hP ij.1).fun_mul (hQ ij.2)

private theorem analyticAt_polynomial_coeff_pow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {P : E → ℂ[X]} {x : E}
    (hP : ∀ j, AnalyticAt ℂ (fun y => (P y).coeff j) x) :
    ∀ n j : ℕ, AnalyticAt ℂ (fun y => (P y ^ n).coeff j) x := by
  intro n
  induction n with
  | zero =>
      intro j
      simpa only [pow_zero] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : ℂ[X]).coeff j) x)
  | succ n ih =>
      intro j
      simp only [pow_succ]
      exact analyticAt_polynomial_coeff_mul ih hP j

private theorem analyticAt_polynomial_coeff_prod {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (P : ι → E → ℂ[X]) {x : E}
    (hP : ∀ i j, AnalyticAt ℂ (fun y => (P i y).coeff j) x) :
    ∀ (s : Finset ι) (j : ℕ), AnalyticAt ℂ (fun y => (∏ i ∈ s, P i y).coeff j) x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro j
      simpa only [Finset.prod_empty] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : ℂ[X]).coeff j) x)
  | @insert i s hi ih =>
      intro j
      simp only [Finset.prod_insert hi]
      exact analyticAt_polynomial_coeff_mul (hP i) ih j

variable {ι : Type*} [Fintype ι]

/-- Every coefficient of the node polynomial is entire in its nodes.-/
theorem analyticAt_nodePolynomial_coeff (m : ι → ℕ) (j : ℕ) (δ : ι → ℂ) :
    AnalyticAt ℂ (fun ε : ι → ℂ => (nodePolynomial ε m).coeff j) δ := by
  have hfactor : ∀ i j,
      AnalyticAt ℂ (fun ε : ι → ℂ => (X - C (ε i)).coeff j) δ := by
    intro i j
    by_cases hj : j = 0
    · subst j
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub, ContinuousLinearMap.proj_apply] using
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt δ).fun_neg
    · simpa only [Polynomial.coeff_sub, Polynomial.coeff_C, ite_eq_right hj, sub_zero] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (X : ℂ[X]).coeff j) δ)
  unfold nodePolynomial
  apply analyticAt_polynomial_coeff_prod
  intro i k
  exact analyticAt_polynomial_coeff_pow (hfactor i) (m i) k

/-- Evaluation of the node polynomial is jointly entire in nodes and argument.-/
theorem analyticAt_nodePolynomial_eval_joint (m : ι → ℕ) (p : (ι → ℂ) × ℂ) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × ℂ => (nodePolynomial q.1 m).eval q.2) p := by
  simp only [nodePolynomial_eval]
  exact Finset.analyticAt_fun_prod _ fun i _ =>
    (analyticAt_snd.fun_sub
      (((ContinuousLinearMap.proj (R := ℂ) i).analyticAt p.1).fun_comp analyticAt_fst)).fun_pow (m i)

end AbelFormalization
