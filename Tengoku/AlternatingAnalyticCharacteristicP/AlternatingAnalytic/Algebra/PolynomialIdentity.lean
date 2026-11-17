import Tengoku.Seed.Algebra.MvPolynomial.Funext
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vector-valued polynomial identity principle

Over an infinite field, a polynomial with finitely many vector coefficients that vanishes
everywhere has all coefficients zero (Lemma B.6). Applying linear functionals reduces this to
`MvPolynomial.funext`. The coefficient space `Y` may be infinite-dimensional.
-/

namespace VectorPolynomial

variable {K Y σ : Type*} [Field K] [AddCommGroup Y] [Module K Y]

/-- Evaluate a polynomial with vector coefficients at a point.-/
noncomputable def eval (c : (σ →₀ ℕ) →₀ Y) (x : σ → K) : Y :=
  c.sum fun α y => (α.prod fun i n => x i ^ n) • y

/-- The scalar polynomial obtained by applying a linear functional to each coefficient.-/
noncomputable def scalarPolynomial (φ : Y →ₗ[K] K) (c : (σ →₀ ℕ) →₀ Y) :
    MvPolynomial σ K :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange φ φ.map_zero c)

/--
@isnad1 id=eq.0h6v.s8.a2fe10072528 from=translated src=- shape=d9b63d36 vocab=1ff30313
-/
@[simp]
theorem scalarPolynomial_coeff (φ : Y →ₗ[K] K) (c : (σ →₀ ℕ) →₀ Y)
    (α : σ →₀ ℕ) : (scalarPolynomial φ c).coeff α = φ (c α) := rfl

/-- Scalar evaluation commutes with applying a linear functional to the coefficients.
@isnad1 id=eq.0h6v.s8.722895882c0a from=translated src=- shape=8e73ccc0 vocab=2ac565df
-/
theorem eval_scalarPolynomial (φ : Y →ₗ[K] K) (c : (σ →₀ ℕ) →₀ Y)
    (x : σ → K) : MvPolynomial.eval x (scalarPolynomial φ c) = φ (eval c x) := by
  classical
  change (Finsupp.mapRange φ φ.map_zero c).sum
      (fun α a => a * α.prod (fun i n => x i ^ n)) =
    φ (c.sum fun α y => (α.prod fun i n => x i ^ n) • y)
  rw [Finsupp.sum_mapRange_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- For finitely many variables, evaluation is the usual monomial sum.
@isnad1 id=eq.0h5v.s8.0082b6431867 from=translated src=- shape=b1618444 vocab=762e185a
-/
theorem eval_eq_sum [Fintype σ] (c : (σ →₀ ℕ) →₀ Y) (x : σ → K) :
    eval c x = ∑ α ∈ c.support, (∏ i, x i ^ α i) • c α := by
  simp only [eval, Finsupp.sum, Finsupp.prod_pow]

end VectorPolynomial
