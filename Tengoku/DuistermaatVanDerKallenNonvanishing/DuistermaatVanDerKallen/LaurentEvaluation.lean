import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.Laurent
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PolynomialCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Evaluation of the algebraic Laurent polynomials used by the main targets,
and explicit polynomial representatives on the closed affine torus. The chosen
representative need not preserve multiplication off the torus; evaluation on
the nonvanishing-coordinate domain does preserve the algebra operations. -/

open scoped BigOperators

namespace DuistermaatVanDerKallen

noncomputable section

/-- The finite Laurent sum, using integer powers in each coordinate.-/
def laurentEval {d : ℕ} (f : MultiLaurent d) (z : Fin d → ℂ) : ℂ :=
  f.coeff.sum fun a c => c * ∏ i, z i ^ a i

/-- A Laurent monomial is multiplicative in its exponent on the open torus.-/
def torusMonomialHom {d : ℕ} (z : Fin d → ℂ) (hz : ∀ i, z i ≠ 0) :
    Multiplicative (Fin d → ℤ) →* ℂ where
  toFun a := ∏ i, z i ^ a.toAdd i
  map_one' := by simp
  map_mul' a b := by
    change (∏ i, z i ^ (a.toAdd i + b.toAdd i)) =
      (∏ i, z i ^ a.toAdd i) * ∏ i, z i ^ b.toAdd i
    simp_rw [zpow_add₀ (hz _)]
    exact Finset.prod_mul_distrib

/-- Evaluation as a complex algebra homomorphism, with its domain hypothesis explicit.-/
def laurentEvalHom {d : ℕ} (z : Fin d → ℂ) (hz : ∀ i, z i ≠ 0) : MultiLaurent d →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin d → ℤ) (torusMonomialHom z hz)

theorem laurentEval_eq_hom {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) : laurentEval f z = laurentEvalHom z hz f := by
  simp [laurentEvalHom, AddMonoidAlgebra.lift_apply', laurentEval, torusMonomialHom]

theorem laurentEval_mul {d : ℕ} (f g : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    laurentEval (f * g) z = laurentEval f z * laurentEval g z := by
  simp only [laurentEval_eq_hom _ hz, map_mul]

theorem laurentEval_pow {d : ℕ} (f : MultiLaurent d) (n : ℕ)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    laurentEval (f ^ n) z = laurentEval f z ^ n := by
  simp only [laurentEval_eq_hom _ hz, map_pow]

/-- Represent one signed coordinate power using the two ambient coordinate halves.-/
def ambientIntegerPower {d : ℕ} (i : Fin d) : ℤ → AmbientPolynomial d
  | .ofNat n => MvPolynomial.X (.inl i) ^ n
  | .negSucc n => MvPolynomial.X (.inr i) ^ (n + 1)

/-- A canonical polynomial representative of a finite Laurent sum.-/
def laurentRepresentative {d : ℕ} (f : MultiLaurent d) : AmbientPolynomial d :=
  f.coeff.sum fun a c => MvPolynomial.C c * ∏ i, ambientIntegerPower i (a i)

@[simp] theorem ambientIntegerPower_eval {d : ℕ} (i : Fin d) (a : ℤ) (z : Fin d → ℂ) :
    ambientEval (ambientIntegerPower i a) (torusEmbed z) = z i ^ a := by
  cases a <;> simp [ambientIntegerPower, ambientEval, torusEmbed, inv_pow]

/-- The representation agrees with the original finite Laurent sum. This identity
also holds for the totalized integer-power expressions at zero coordinates.-/
theorem laurentRepresentative_eval {d : ℕ} (f : MultiLaurent d) (z : Fin d → ℂ) :
    ambientEval (laurentRepresentative f) (torusEmbed z) = laurentEval f z := by
  classical
  simp only [laurentRepresentative, Finsupp.sum, ambientEval, map_sum, map_mul,
    MvPolynomial.eval_C, map_prod]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact ambientIntegerPower_eval i (a i) z

/-- The analytic function associated with any algebraic Laurent polynomial has
an explicit ambient polynomial representative, in every finite rank.-/
theorem laurentEval_eq_polynomial_restriction {d : ℕ} (f : MultiLaurent d) :
    laurentEval f = ambientEval (laurentRepresentative f) ∘ torusEmbed := by
  funext z
  exact (laurentRepresentative_eval f z).symm

/-- Regression: a negative lattice generator evaluates as the inverse coordinate.-/
theorem laurentEval_inverse_coordinate {d : ℕ} (i : Fin d) (z : Fin d → ℂ) :
    laurentEval (AddMonoidAlgebra.single (Pi.single i (-1)) 1) z = (z i)⁻¹ := by
  classical
  simp [laurentEval, Pi.single_apply, apply_ite]

end
end DuistermaatVanDerKallen
