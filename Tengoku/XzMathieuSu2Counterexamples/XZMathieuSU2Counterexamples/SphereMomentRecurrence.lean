import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.SphereMonomials
import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.PolynomialIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Rotation recurrences and factorial formulas for mixed squared-coordinate sphere moments. -/

noncomputable section
open MeasureTheory Polynomial
namespace XZMathieuSU2Counterexamples.Hopf

def firstCoordinate : C(Sphere, ℂ) := ⟨fun z => z.val.1, continuous_subtype_val.fst⟩
def secondCoordinate : C(Sphere, ℂ) := ⟨fun z => z.val.2, continuous_subtype_val.snd⟩

/--
@isnad1 id=eq.0h1v.s5.e440b8083614 from=translated src=- shape=ff785da3 vocab=38011761
-/
@[simp] theorem firstCoordinate_apply (z : Sphere) : firstCoordinate z = z.val.1 := rfl
/--
@isnad1 id=eq.0h1v.s5.f8a7f5f8eccc from=translated src=- shape=ff785da3 vocab=0168825e
-/
@[simp] theorem secondCoordinate_apply (z : Sphere) : secondCoordinate z = z.val.2 := rfl

def rotationMomentPolynomial (p q : ℕ) : Polynomial C(Sphere, ℂ) :=
  (C firstCoordinate - X * C secondCoordinate) ^ (p + 1) *
    (C (star firstCoordinate) - X * C (star secondCoordinate)) ^ p *
    (X * C firstCoordinate + C secondCoordinate) ^ q *
    (X * C (star firstCoordinate) + C (star secondCoordinate)) ^ (q + 1)

/--
@isnad1 id=eq.0h4v.s7.588d7d068f49 from=translated src=- shape=65dcedd6 vocab=5e623302
-/
theorem rotationMomentPolynomial_eval (p q : ℕ) (t : ℝ) (z : Sphere) :
    (rotationMomentPolynomial p q).eval (ContinuousMap.const Sphere (t : ℂ)) z =
      coordinateMonomial (p + 1) p q (q + 1) (scaledSU2Action (1, (t : ℂ)) z.val) := by
  simp [rotationMomentPolynomial, coordinateMonomial, scaledSU2Action]
  ring

/--
@isnad1 id=eq.0h2v.s4.e6ec5cd3bafa from=translated src=- shape=8815bf63 vocab=b2d52f5f
-/
theorem rotationMomentPolynomial_integral_zero (p q : ℕ) :
    integrateCoefficients (rotationMomentPolynomial p q) = 0 := by
  apply integrateCoefficients_eq_zero
  intro t
  simp_rw [rotationMomentPolynomial_eval]
  exact coordinateMonomial_scaled_integral_zero (p + 1) p q (q + 1) (by omega) _

/--
@isnad1 id=eq.0h3v.s8.2e063e76ec28 from=translated src=- shape=55734841 vocab=07fe151b
-/
theorem rotationMomentPolynomial_coeff_one (p q : ℕ) (z : Sphere) :
    (rotationMomentPolynomial p q).coeff 1 z =
      -(p + 1 : ℂ) * sphereMonomial p p (q + 1) (q + 1) z -
      (p : ℂ) * sphereMonomial (p + 1) (p - 1) q (q + 2) z +
      (q : ℂ) * sphereMonomial (p + 2) p (q - 1) (q + 1) z +
      (q + 1 : ℂ) * sphereMonomial (p + 1) (p + 1) q q z := by
  have hc (f : Polynomial C(Sphere, ℂ)) : f.coeff 1 = f.derivative.eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simp
  rw [hc]
  simp only [rotationMomentPolynomial, derivative_mul, derivative_pow, derivative_sub,
    derivative_add, derivative_C, derivative_X, eval_mul, eval_add, eval_sub, eval_pow,
    eval_C, eval_X, eval_zero]
  simp [sphereMonomial, coordinateMonomial, pow_succ]
  ring

def mixedMoment (p q : ℕ) : ℂ := ∫ z, sphereMonomial p p q q z ∂surfaceMeasure

/--
@isnad1 id=integrab.0h4v.s5.d92ede780b86 from=translated src=- shape=3586a20f vocab=6922b13b
-/
theorem sphereMonomial_integrable (α β γ δ : ℕ) :
    Integrable (sphereMonomial α β γ δ) surfaceMeasure :=
  (continuous_sphereMonomial α β γ δ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/--
@isnad1 id=eq.0h2v.s6.5e79152e7a6d from=translated src=- shape=862f52a9 vocab=75b53e31
-/
theorem mixedMoment_balance (p q : ℕ) :
    (q + 1 : ℂ) * mixedMoment (p + 1) q = (p + 1 : ℂ) * mixedMoment p (q + 1) := by
  have h := congrArg (fun f : Polynomial ℂ => f.coeff 1)
    (rotationMomentPolynomial_integral_zero p q)
  rw [integrateCoefficients_coeff, coeff_zero] at h
  simp_rw [rotationMomentPolynomial_coeff_one] at h
  have h1 := (sphereMonomial_integrable p p (q + 1) (q + 1)).const_mul (-(p + 1 : ℂ))
  have h2 := (sphereMonomial_integrable (p + 1) (p - 1) q (q + 2)).const_mul (p : ℂ)
  have h3 := (sphereMonomial_integrable (p + 2) p (q - 1) (q + 1)).const_mul (q : ℂ)
  have h4 := (sphereMonomial_integrable (p + 1) (p + 1) q q).const_mul (q + 1 : ℂ)
  have hsum := integral_add ((h1.sub h2).add h3) h4
  have hsum' := integral_add (h1.sub h2) h3
  have hsub := integral_sub h1 h2
  simp only [Pi.add_apply, Pi.sub_apply] at hsum hsum' hsub
  rw [hsum, hsum', hsub] at h
  simp_rw [integral_const_mul] at h
  rw [sphereMonomial_integral_zero (p + 1) (p - 1) q (q + 2) (by omega),
    sphereMonomial_integral_zero (p + 2) p (q - 1) (q + 1) (by omega)] at h
  unfold mixedMoment
  linear_combination h

/--
@isnad1 id=eq.0h2v.s5.9d6963ef35df from=translated src=- shape=8bafeeb3 vocab=c1775d74
-/
theorem mixedMoment_partition (p q : ℕ) :
    mixedMoment p q = mixedMoment (p + 1) q + mixedMoment p (q + 1) := by
  have hpoint (z : Sphere) : sphereMonomial p p q q z =
      sphereMonomial (p + 1) (p + 1) q q z + sphereMonomial p p (q + 1) (q + 1) z := by
    have hz : z.val.1 * star z.val.1 + z.val.2 * star z.val.2 = 1 := by
      simpa [a, Complex.normSq_eq_conj_mul_self, mul_comm] using congrArg Complex.ofReal z.property
    simp only [sphereMonomial, coordinateMonomial, pow_succ]
    linear_combination -z.val.1 ^ p * star z.val.1 ^ p * z.val.2 ^ q * star z.val.2 ^ q * hz
  unfold mixedMoment
  simp_rw [hpoint]
  exact integral_add (sphereMonomial_integrable (p + 1) (p + 1) q q)
    (sphereMonomial_integrable p p (q + 1) (q + 1))

/--
@isnad1 id=eq.0h0v.s4.173ed312fe17 from=translated src=- shape=8640e5ff vocab=8bc279e5
-/
theorem mixedMoment_zero_zero : mixedMoment 0 0 = 1 := by
  simp [mixedMoment, sphereMonomial, coordinateMonomial]

/--
@isnad1 id=eq.0h2v.s6.3d9d034d0c59 from=translated src=- shape=892a4112 vocab=969ac44a
-/
theorem mixedMoment_succ_left (p q : ℕ) :
    mixedMoment (p + 1) q = (p + 1 : ℂ) / (p + q + 2 : ℂ) * mixedMoment p q := by
  have hn : (p + q + 2 : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : p + q + 2 ≠ 0)
  apply (mul_left_cancel₀ hn)
  field_simp
  linear_combination -(p + 1 : ℂ) * mixedMoment_partition p q + mixedMoment_balance p q

/--
@isnad1 id=eq.0h2v.s6.6125d4253b15 from=translated src=- shape=53ec8b96 vocab=969ac44a
-/
theorem mixedMoment_succ_right (p q : ℕ) :
    mixedMoment p (q + 1) = (q + 1 : ℂ) / (p + q + 2 : ℂ) * mixedMoment p q := by
  have hn : (p + q + 2 : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : p + q + 2 ≠ 0)
  apply (mul_left_cancel₀ hn)
  field_simp
  linear_combination -(q + 1 : ℂ) * mixedMoment_partition p q - mixedMoment_balance p q

/-- Exact mixed squared-coordinate moments of normalized surface measure.
@isnad1 id=eq.0h2v.s5.f90494092224 from=translated src=- shape=055fdabe vocab=a407ef2b
-/
theorem mixedMoment_factorial (p q : ℕ) :
    mixedMoment p q = (p.factorial : ℂ) * q.factorial / (p + q + 1).factorial := by
  have hf (n : ℕ) : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  induction p with
  | zero =>
    induction q with
    | zero => simp [mixedMoment_zero_zero]
    | succ q ih =>
      rw [mixedMoment_succ_right, ih]
      simp only [Nat.zero_add, Nat.factorial_zero, Nat.cast_one, one_mul,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
      have hq : (q + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : q + 1 ≠ 0)
      have hq' : (q + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : q + 2 ≠ 0)
      field_simp
      ring
  | succ p ih =>
    rw [mixedMoment_succ_left, ih]
    rw [show p + 1 + q + 1 = (p + q + 1) + 1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hpq : (p + q + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : p + q + 1 ≠ 0)
    have hpq' : (p + q + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : p + q + 2 ≠ 0)
    have hadd : (p : ℂ) + q + 1 + 1 = p + q + 2 := by ring
    field_simp [hf, hpq, hpq', hadd]
    ring

end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/SphereMomentRecurrence.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
