import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Statement
import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.EntireSinc
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators
open Set Polynomial

namespace Erdos1133

/-- Bernstein growth class with an arbitrary finite complex prefactor.-/
def IsBernsteinFunction (σ H : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ (∀ t : ℝ, ‖f t‖ ≤ H) ∧
    ∃ K > (0 : ℝ), ∀ z : ℂ, ‖f z‖ ≤ K * Real.exp (σ * |z.im|)

def polynomialPullback (D : ℝ) (P : ℝ[X]) (z : ℂ) : ℂ :=
  (P.map Complex.ofRealHom).eval (Complex.cos ((Real.pi / D : ℝ) * z))

theorem polynomialPullback_entire (D : ℝ) (P : ℝ[X]) :
    Differentiable ℂ (polynomialPullback D P) := by
  unfold polynomialPullback
  fun_prop

theorem polynomialPullback_real (D : ℝ) (P : ℝ[X]) (t : ℝ) :
    polynomialPullback D P t = ((P.eval (Real.cos (Real.pi / D * t)) : ℝ) : ℂ) := by
  unfold polynomialPullback
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cos]
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply Complex.ofRealHom _

theorem polynomialPullback_at_node {D : ℝ} (hD : 0 < D)
    (P : ℝ[X]) (x : Icc (-1 : ℝ) 1) :
    polynomialPullback D P (angularNode D x) = ((P.eval (x : ℝ) : ℝ) : ℂ) := by
  rw [polynomialPullback_real, cos_angularNode hD]

theorem polynomialPullback_bound_real (D : ℝ) (P : ℝ[X]) (H : ℝ)
    (hP : BoundedOnSegment H P) (t : ℝ) :
    ‖polynomialPullback D P t‖ ≤ H := by
  rw [polynomialPullback_real, Complex.norm_real, Real.norm_eq_abs]
  exact hP _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

private theorem mapped_polynomial_bound (P : ℝ[X]) (w : ℂ) (a : ℝ)
    (ha : 0 ≤ a) (hw : ‖w‖ ≤ Real.exp a) :
    ‖(P.map Complex.ofRealHom).eval w‖ ≤
      (∑ j ∈ P.support, |P.coeff j|) * Real.exp ((P.natDegree : ℝ) * a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum]
  unfold Polynomial.sum
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul, norm_pow, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    ‖w‖ ^ j ≤ (Real.exp a) ^ j := pow_le_pow_left₀ (norm_nonneg _) hw j
    _ = Real.exp ((j : ℝ) * a) := (Real.exp_nat_mul a j).symm
    _ ≤ Real.exp ((P.natDegree : ℝ) * a) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ ha
      exact_mod_cast Polynomial.le_natDegree_of_mem_supp j hj

theorem polynomialPullback_isBernstein {D H : ℝ} (hD : 0 < D)
    (P : ℝ[X]) (hdeg : (P.natDegree : ℝ) ≤ D) (hP : BoundedOnSegment H P) :
    IsBernsteinFunction Real.pi H (polynomialPullback D P) := by
  refine ⟨polynomialPullback_entire D P, polynomialPullback_bound_real D P H hP, ?_⟩
  let K : ℝ := 1 + ∑ j ∈ P.support, |P.coeff j|
  have hsum : 0 ≤ ∑ j ∈ P.support, |P.coeff j| := Finset.sum_nonneg (by intros; positivity)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro z
  have hfreq : 0 < Real.pi / D := div_pos Real.pi_pos hD
  have him : |(((Real.pi / D : ℝ) : ℂ) * z).im| = Real.pi / D * |z.im| := by
    simp [abs_mul, abs_of_pos hfreq]
  have hw := Erdos1152.V5.norm_complex_cos_le (((Real.pi / D : ℝ) : ℂ) * z)
  rw [him] at hw
  have hb := mapped_polynomial_bound P _ _ (mul_nonneg hfreq.le (abs_nonneg _)) hw
  have hrate : (P.natDegree : ℝ) * (Real.pi / D * |z.im|) ≤ Real.pi * |z.im| := by
    calc
      (P.natDegree : ℝ) * (Real.pi / D * |z.im|) ≤ D * (Real.pi / D * |z.im|) :=
        mul_le_mul_of_nonneg_right hdeg (mul_nonneg hfreq.le (abs_nonneg _))
      _ = Real.pi * |z.im| := by field_simp
  apply hb.trans
  apply mul_le_mul
  · dsimp [K]; linarith
  · exact Real.exp_le_exp.mpr hrate
  · positivity
  · dsimp [K]; positivity

end Erdos1133
