import Tengoku.WasowAsymptoticsLean.NormalFormGoal
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
import Tengoku.Seed.Analysis.Complex.RealDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowPolynomialPhase.zeroConstantPrimitive_coeff_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPolynomialPhase.derivative_zeroConstantPrimitive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPolynomialPhase.rootOnRay_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPolynomialPhase.phase_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Polynomial phases for the unramified scalar rational normal form.  The primitive
is constructed coefficient by coefficient, has constant coefficient zero, and
its ray derivative includes the actual complex direction factor.
-/
set_option autoImplicit false
noncomputable section
open Polynomial
open CRGNormalFormGoal

namespace WasowPolynomialPhase

/-- The polynomial primitive whose constant coefficient vanishes.-/
def zeroConstantPrimitive (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ n ∈ P.support, monomial (n + 1) (P.coeff n / ((n + 1 : ℕ) : ℂ))

theorem zeroConstantPrimitive_coeff_zero (P : Polynomial ℂ) :
    (zeroConstantPrimitive P).coeff 0 = 0 := by
  simp [zeroConstantPrimitive, coeff_monomial]

theorem derivative_zeroConstantPrimitive (P : Polynomial ℂ) :
    (zeroConstantPrimitive P).derivative = P := by
  classical
  unfold zeroConstantPrimitive
  simp only [derivative_sum, derivative_monomial_succ]
  have hterm (n : ℕ) : P.coeff n / ((n + 1 : ℕ) : ℂ) * (n + 1) = P.coeff n := by
    rw [Nat.cast_add, Nat.cast_one]
    exact div_mul_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero n)
  simp only [hterm]
  exact P.sum_monomial_eq

theorem rootOnRay_one (θ r : ℝ) : rootOnRay 1 θ (0 : Fin 1) r = ray θ r := by
  simp [rootOnRay, ray]

theorem phase_hasDerivAt (P : Polynomial ℂ) (θ r : ℝ) :
    HasDerivAt (phaseOnRay 1 (zeroConstantPrimitive P) θ (0 : Fin 1))
      (Complex.exp ((θ : ℂ) * Complex.I) * P.eval (ray θ r)) r := by
  have hcomplex := ((zeroConstantPrimitive P).hasDerivAt (ray θ r)).comp (r : ℂ)
    ((hasDerivAt_id (r : ℂ)).mul_const (Complex.exp ((θ : ℂ) * Complex.I)))
  have hreal := hcomplex.comp_ofReal
  change HasDerivAt (fun t => (zeroConstantPrimitive P).eval (rootOnRay 1 θ 0 t)) _ r
  simp_rw [rootOnRay_one]
  simpa only [derivative_zeroConstantPrimitive, Function.comp_apply, id_eq,
    one_mul, mul_one, ray, mul_comm] using hreal

end WasowPolynomialPhase

