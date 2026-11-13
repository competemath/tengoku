import Tengoku.Nlalib.NLAlib.Polynomial.BestApproximation.InterpolationPeakMaxima
import Tengoku.Nlalib.NLAlib.Polynomial.BestApproximation.NodeSimplex
import Tengoku.Seed.Analysis.Calculus.ContDiff.Polynomial
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth dependence of signed interpolation polynomials on their nodes

Distinct-node cardinal products are rational functions of the interior node
coordinates. Fixed-grid reconstruction supplies the same regularity for spatial
derivatives without differentiating varying polynomial coefficients.
-/

noncomputable section
open Polynomial Real Finset Set Filter
open scoped Topology ContDiff
namespace NLAlib

/-- Every canonical node is an affine, hence smooth, function of its interior coordinates.
Source: endpoint-fixed node parametrization; focused reroutes, peak charts.
@isnad1 id=contdiff.0h3v.s6.c5093cdf2ab1 from=translated src=- shape=8a0c9af7 vocab=7cc86f57
-/
theorem contDiff_canonicalIntervalNodes (n : ℕ) (j : Fin (n + 2)) (r : ℕ∞ω) :
    ContDiff ℝ r (fun t : Fin n → ℝ => canonicalIntervalNodes n t j) := by
  refine Fin.cases (by simp only [canonicalIntervalNodes_zero]; fun_prop) (fun k => ?_) j
  refine Fin.lastCases (by simpa using (contDiff_const : ContDiff ℝ r (fun _ : Fin n → ℝ => (1 : ℝ))))
    (fun k => ?_) k
  simpa only [canonicalIntervalNodes_interior] using (contDiff_apply ℝ ℝ k : ContDiff ℝ r (fun t : Fin n → ℝ => t k))

/-- The actual gap polynomial is the finite rational cardinal formula.
Source: Lagrange interpolation; focused reroutes, smooth peak coordinates.
@isnad1 id=eq.0h4v.s7.911ac40bb8a0 from=translated src=- shape=07093ccd vocab=efd00a9f
-/
theorem eval_interpolationGapPolynomial_eq_sum_prod (n : ℕ) (t : Fin n → ℝ)
    (i : Fin (n + 1)) (x : ℝ) :
    (interpolationGapPolynomial n t i).eval x = ∑ j : Fin (n + 2), interpolationGapSign n i j *
      ∏ k ∈ univ.erase j, (x - canonicalIntervalNodes n t k) /
        (canonicalIntervalNodes n t j - canonicalIntervalNodes n t k) := by
  simp only [interpolationGapPolynomial, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    eval_lagrange_basis_eq_prod_div]

/-- Joint evaluation of the actual signed gap polynomial is smooth at every
ordered node configuration and every real evaluation point.
Source: distinct-node rational cardinal products; focused reroutes, peak charts.
@isnad1 id=contdiff.1h5v.s7.7e563c892e65 from=translated src=- shape=54b8cd64 vocab=23c89b88
-/
theorem contDiffAt_eval_interpolationGapPolynomial {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) (x : ℝ) (r : ℕ∞ω) :
    ContDiffAt ℝ r (fun u : (Fin n → ℝ) × ℝ => (interpolationGapPolynomial n u.1 i).eval u.2) (t, x) := by
  have hn (j : Fin (n + 2)) : ContDiffAt ℝ r
      (fun u : (Fin n → ℝ) × ℝ => canonicalIntervalNodes n u.1 j) (t, x) :=
    (contDiff_canonicalIntervalNodes n j r).contDiffAt.comp (t, x) contDiffAt_fst
  simp_rw [eval_interpolationGapPolynomial_eq_sum_prod]
  apply ContDiffAt.sum
  intro j _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro k hk
  apply (contDiffAt_snd.sub (hn k)).div ((hn j).sub (hn k))
  exact sub_ne_zero.mpr (fun h => (mem_erase.mp hk).1 (ht.injective h.symm))

/-- The spatial derivative of the actual gap polynomial depends smoothly
on both the ordered node coordinates and its evaluation point.
Source: differentiating the finite rational cardinal formula; focused reroutes, implicit peak charts.
@isnad1 id=contdiff.1h5v.s8.20da3e00a303 from=translated src=- shape=0a8bf445 vocab=95df23ce
-/
theorem contDiffAt_eval_derivative_interpolationGapPolynomial {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) (x : ℝ) (r : ℕ∞ω) :
    ContDiffAt ℝ r (fun u : (Fin n → ℝ) × ℝ =>
      (interpolationGapPolynomial n u.1 i).derivative.eval u.2) (t, x) := by
  have hbase := contDiffAt_eval_interpolationGapPolynomial ht i x (r + 1)
  have hf : ContDiffAt ℝ (r + 1) (fun p : ((Fin n → ℝ) × ℝ) × ℝ =>
      (interpolationGapPolynomial n p.1.1 i).eval p.2) ((t, x), x) := by
    exact hbase.comp ((t, x), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd := ContDiffAt.fderiv_succ
    (f := fun (u : (Fin n → ℝ) × ℝ) (y : ℝ) => (interpolationGapPolynomial n u.1 i).eval y)
    (g := fun u : (Fin n → ℝ) × ℝ => u.2) (x₀ := (t, x)) (m := r) hf contDiffAt_snd
  have heval := hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  have heq : (fun u : (Fin n → ℝ) × ℝ =>
      (fderiv ℝ (fun y => (interpolationGapPolynomial n u.1 i).eval y) u.2) 1) =
      (fun u => (interpolationGapPolynomial n u.1 i).derivative.eval u.2) := by
    funext u
    rw [(interpolationGapPolynomial n u.1 i).hasFDerivAt u.2 |>.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
      one_smul]
  rw [heq] at heval
  exact heval

end NLAlib
