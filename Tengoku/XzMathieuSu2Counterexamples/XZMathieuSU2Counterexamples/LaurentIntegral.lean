import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.Basic
import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.Bernstein
import Tengoku.Seed.Analysis.Convex.Hull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open MeasureTheory Polynomial
namespace XZMathieuSU2Counterexamples

abbrev Laurent := LaurentPolynomial ℂ[X]

def specialize (x : ℂ) : Laurent →+* ScalarLaurent :=
  AddMonoidAlgebra.mapRingHom ℤ (Polynomial.evalRingHom x)

/--
@isnad1 id=eq.0h3v.s7.851a662b7bdb from=translated src=- shape=7e819739 vocab=22456d81
-/
@[simp] theorem specialize_coeff (x : ℂ) (f : Laurent) (k : ℤ) :
    (specialize x f).coeff k = (f.coeff k).eval x := by simp [specialize]

/--
@isnad1 id=eq.0h2v.s7.72352be584af from=translated src=- shape=8b80924c vocab=a29d7125
-/
@[simp] theorem specialize_C (x : ℂ) (f : ℂ[X]) :
    specialize x (LaurentPolynomial.C f) = LaurentPolynomial.C (f.eval x) := by
  ext n
  simp only [specialize_coeff, LaurentPolynomial.C_apply]
  split_ifs <;> simp

/--
@isnad1 id=eq.0h2v.s6.c372f2e25a68 from=translated src=- shape=f8b81a1b vocab=0d57680a
-/
@[simp] theorem specialize_T (x : ℂ) (n : ℤ) :
    specialize x (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ (Polynomial.evalRingHom x)
    (AddMonoidAlgebra.single n 1) = AddMonoidAlgebra.single n 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

def integral (f : Laurent) : ℂ := ∫ x in (0 : ℝ)..1, (f.coeff 0).eval (x : ℂ)

def integralLinear : Laurent →ₗ[ℂ] ℂ where
  toFun := integral
  map_add' f g := by
    simp only [integral, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, eval_add]
    exact intervalIntegral.integral_add
      ((f.coeff 0).continuous.comp Complex.continuous_ofReal |>.intervalIntegrable 0 1)
      ((g.coeff 0).continuous.comp Complex.continuous_ofReal |>.intervalIntegrable 0 1)
  map_smul' c f := by
    simp [integral, intervalIntegral.integral_const_mul]

/-- The conjecture in one interval and one torus variable.-/
def XZConjecture : Prop := ∀ f : Laurent,
  (∀ n : ℕ, 1 ≤ n → integral (f ^ n) = 0) →
  (0 : ℝ) ∉ convexHull ℝ ((fun k : ℤ => (k : ℝ)) '' (f.coeff.support : Set ℤ))

end XZMathieuSU2Counterexamples
