import Tengoku.AbelFormalization.AbelFormalization.HermiteInterpolation
import Tengoku.AbelFormalization.AbelFormalization.NormalizedPolynomial
import Tengoku.Seed.Analysis.Calculus.Deriv.CompMul
import Tengoku.Seed.Algebra.Polynomial.Eval.Degree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Scaling Hermite interpolants

Nonzero complex scaling preserves the combined multiplicity of every node.
Local equality `f(z) = g(q*z)` therefore identifies the two interpolating
polynomials by uniqueness. Their factorial-normalized coefficients differ by
the factor `q^r`, independently of the contours used to construct them.
-/

noncomputable section

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

/-- Complex scalar substitution commutes with iterated derivatives, including
zero scale, without a differentiability hypothesis.
@isnad1 id=eq.0h3v.s6.89df5cf9fcd1 from=translated src=- shape=6dd1e735 vocab=0e49d76f
-/
theorem iteratedDeriv_comp_mul_complex (f : ℂ → ℂ) (q : ℂ) (r : ℕ) :
    iteratedDeriv r (fun z => f (q * z)) =
      fun z => q ^ r * iteratedDeriv r f (q * z) := by
  induction r with
  | zero => simp
  | succ r ih =>
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul, ← iteratedDeriv_succ, pow_succ]
    ring

/--
@isnad1 id=eq.1h2v.s6.4680d640451f from=translated src=- shape=671c7356 vocab=45c84cb6
-/
theorem degree_comp_scale (P : ℂ[X]) {q : ℂ} (hq : q ≠ 0) :
    (P.comp (C q * X)).degree = P.degree := by
  rw [Polynomial.degree_comp (by simp [degree_C_mul_X hq]), degree_C_mul_X hq, mul_one]

variable {ι : Type*} [Fintype ι]

/-- Nonzero scaling preserves collisions and their summed multiplicities.
@isnad1 id=eq.1h5v.s5.ec1d408399c3 from=translated src=- shape=074f5b67 vocab=337280c4
-/
theorem nodeMultiplicity_scale (δ : ι → ℂ) (m : ι → ℕ) {q : ℂ} (hq : q ≠ 0)
    (ξ : ℂ) :
    nodeMultiplicity (fun i => q * δ i) m (q * ξ) = nodeMultiplicity δ m ξ := by
  classical
  simp only [nodeMultiplicity, mul_right_inj' hq]

/-- A local scaling identity at every supplied node identifies any pair of
Hermite interpolants. No distinctness of the nodes is required.
@isnad1 id=eq.6h8v.s8.741d717a6cce from=translated src=- shape=16453f5b vocab=af937f76
-/
theorem polynomial_eq_comp_scale_of_grouped_jets
    (δ : ι → ℂ) (m : ι → ℕ) {q : ℂ} (hq : q ≠ 0)
    {f g : ℂ → ℂ} {P Q : ℂ[X]}
    (hPdegree : P.degree < (totalMultiplicity m : WithBot ℕ))
    (hQdegree : Q.degree < (totalMultiplicity m : WithBot ℕ))
    (hPjets : ∀ ξ r, r < nodeMultiplicity δ m ξ →
      iteratedDeriv r f ξ = iteratedDeriv r (fun z => P.eval z) ξ)
    (hQjets : ∀ ξ r, r < nodeMultiplicity (fun i => q * δ i) m ξ →
      iteratedDeriv r g ξ = iteratedDeriv r (fun z => Q.eval z) ξ)
    (hlocal : ∀ i, f =ᶠ[𝓝 (δ i)] fun z => g (q * z)) :
    P = Q.comp (C q * X) := by
  apply polynomial_eq_of_grouped_jets δ m hPdegree
    (by simpa only [degree_comp_scale Q hq] using hQdegree)
  intro ξ r hr
  obtain ⟨i, hi, _⟩ := (nodeMultiplicity_pos_iff δ m ξ).mp
    ((Nat.zero_le r).trans_lt hr)
  have he : f =ᶠ[𝓝 ξ] fun z => g (q * z) := hi ▸ hlocal i
  have hscaled : r < nodeMultiplicity (fun i => q * δ i) m (q * ξ) := by
    rwa [nodeMultiplicity_scale δ m hq]
  have heval : (fun z => (Q.comp (C q * X)).eval z) =
      (fun z => Q.eval (q * z)) := by
    funext z
    simp
  rw [heval, iteratedDeriv_comp_mul_complex (fun z => Q.eval z) q r]
  calc
    _ = iteratedDeriv r f ξ := (hPjets ξ r hr).symm
    _ = iteratedDeriv r (fun z => g (q * z)) ξ := he.iteratedDeriv_eq r
    _ = q ^ r * iteratedDeriv r g (q * ξ) :=
      congrFun (iteratedDeriv_comp_mul_complex g q r) ξ
    _ = _ := congrArg (fun v => q ^ r * v) (hQjets (q * ξ) r hscaled)

end AbelFormalization
