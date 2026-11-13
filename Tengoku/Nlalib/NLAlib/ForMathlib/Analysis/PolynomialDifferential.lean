import Tengoku.Seed.Analysis.Calculus.FDeriv.Pow
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differentiation of polynomial evaluation in a noncommutative algebra

The derivative is the finite sum with every possible insertion position.
No commutativity of the input algebra is assumed. This supports the
matrix divided-difference and rational block calculi.
-/

noncomputable section
open scoped RightActions
namespace Polynomial
variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The derivative of polynomial evaluation in an arbitrary normed algebra,
as a finite sum of continuous linear insertion maps.-/
def frechetDerivative (p : 𝕜[X]) (x : A) : A →L[𝕜] A :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k •
    ∑ j ∈ Finset.range k,
      x ^ (k.pred - j) •> ContinuousLinearMap.id 𝕜 A <• x ^ j

/-- Evaluation of the polynomial derivative is the sum of products with
one occurrence of the direction at every insertion position.
@isnad1 id=eq.0h5v.s8.f58a5553fe25 from=translated src=- shape=4fc7ae7e vocab=b40881ac
-/
theorem frechetDerivative_apply (p : 𝕜[X]) (x h : A) :
    frechetDerivative p x h = ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k • ∑ j ∈ Finset.range k, x ^ (k.pred - j) * h * x ^ j := by
  simp [frechetDerivative, mul_assoc]

/-- Polynomial evaluation has the insertion-sum Fréchet derivative even
when the target algebra is noncommutative.
@isnad1 id=hasfderi.0h4v.s8.3be700ffc817 from=translated src=- shape=5cf08942 vocab=cad1a5d3
-/
theorem hasFDerivAt_aeval_noncomm (p : 𝕜[X]) (x : A) :
    HasFDerivAt (fun y : A => aeval y p) (frechetDerivative p x) x := by
  have heq : (fun y : A => aeval y p) =
      fun y => ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • y ^ k := by
    funext y
    rw [aeval_eq_sum_range]
  rw [heq]
  exact HasFDerivAt.fun_sum (fun k _ => (hasFDerivAt_pow' k).const_smul (p.coeff k))

/-- Constants have zero polynomial evaluation derivative.
@isnad1 id=eq.0h4v.s9.437aafd50643 from=translated src=- shape=1219aab2 vocab=ab7045d7
-/
@[simp] theorem frechetDerivative_C (c : 𝕜) (x : A) :
    frechetDerivative (C c) x = 0 := by
  apply (hasFDerivAt_aeval_noncomm (C c) x).unique
  convert! (hasFDerivAt_const (𝕜 := 𝕜) (algebraMap 𝕜 A c) x) using 1
  simp only [aeval_C]

/-- The derivative of the variable polynomial is the identity map.
@isnad1 id=eq.0h3v.s7.ec1e50bed411 from=translated src=- shape=7079942f vocab=c25bdddb
-/
@[simp] theorem frechetDerivative_X (x : A) :
    frechetDerivative (X : 𝕜[X]) x = ContinuousLinearMap.id 𝕜 A := by
  apply (hasFDerivAt_aeval_noncomm (X : 𝕜[X]) x).unique
  convert! (hasFDerivAt_id (𝕜 := 𝕜) x) using 1
  funext y
  exact aeval_X y

/-- The insertion derivative is additive in the polynomial.
@isnad1 id=eq.0h5v.s9.a0c4087a2a66 from=translated src=- shape=ae388a16 vocab=1cfe10fb
-/
@[simp] theorem frechetDerivative_add (p q : 𝕜[X]) (x : A) :
    frechetDerivative (p + q) x = frechetDerivative p x + frechetDerivative q x := by
  apply (hasFDerivAt_aeval_noncomm (p + q) x).unique
  convert! (hasFDerivAt_aeval_noncomm p x).add (hasFDerivAt_aeval_noncomm q x) using 1
  funext y
  exact map_add (aeval y) p q

/-- The polynomial derivative obeys the noncommutative product rule.
@isnad1 id=eq.0h5v.s11.5feed5608093 from=translated src=- shape=19c9a707 vocab=8f5adedf
-/
theorem frechetDerivative_mul (p q : 𝕜[X]) (x : A) :
    frechetDerivative (p * q) x =
      aeval x p •> frechetDerivative q x + frechetDerivative p x <• aeval x q := by
  apply (hasFDerivAt_aeval_noncomm (p * q) x).unique
  convert! (hasFDerivAt_aeval_noncomm p x).mul' (hasFDerivAt_aeval_noncomm q x) using 1
  funext y
  exact map_mul (aeval y) p q

/-- Algebra homomorphisms transport each insertion in a polynomial
derivative, without requiring continuity of the homomorphism.
@isnad1 id=eq.0h7v.s9.c4d18b5c58b6 from=translated src=- shape=aed703a6 vocab=b74f4fc1
-/
theorem map_frechetDerivative_apply {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]
    (f : A →ₐ[𝕜] B) (p : 𝕜[X]) (x h : A) :
    f (p.frechetDerivative x h) = p.frechetDerivative (f x) (f h) := by
  simp only [frechetDerivative_apply, map_sum, map_smul, map_mul, map_pow]

end Polynomial
