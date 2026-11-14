import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing
import Tengoku.Seed.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive coefficients of a four-factor quadratic L-series

The product is Dirichlet convolution, not pointwise multiplication. At a
prime where one character is negative, pairing its zeta convolution with
the twisted copy makes the even-exponent support explicit. At every other
prime the relevant twist is nonnegative. These finite identities prove
nonnegative real coefficients and the square-coefficient lower bound.
-/

noncomputable section

open ArithmeticFunction Finset
open scoped ComplexOrder

namespace TwinPrime.Analytic

def quadraticProductCoefficients {Q : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ Q) :
    ArithmeticFunction ℂ :=
  .zeta * toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
    toArithmeticFunction ((χ₁ * χ₂) ·)

/--
@isnad1 id=ismultip.0h3v.s5.d764125a1f5b from=translated src=- shape=bd7f30ff vocab=4f001a3d
-/
theorem quadraticProductCoefficients_isMultiplicative {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) :
    (quadraticProductCoefficients χ₁ χ₂).IsMultiplicative :=
  ((χ₁.isMultiplicative_zetaMul.mul χ₂.isMultiplicative_toArithmeticFunction).mul
    (χ₁ * χ₂).isMultiplicative_toArithmeticFunction)

/--
@isnad1 id=eq.0h3v.s5.7aaa9a66b439 from=translated src=- shape=756fba0b vocab=575c4b5f
-/
@[simp] theorem quadraticProductCoefficients_one {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) : quadraticProductCoefficients χ₁ χ₂ 1 = 1 :=
  (quadraticProductCoefficients_isMultiplicative χ₁ χ₂).map_one

/--
@isnad1 id=eq.0h3v.s5.5c855f2e2aad from=translated src=- shape=bc651f2d vocab=d4e90ed4
-/
theorem quadraticProductCoefficients_comm {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) :
    quadraticProductCoefficients χ₁ χ₂ = quadraticProductCoefficients χ₂ χ₁ := by
  unfold quadraticProductCoefficients
  rw [show χ₂ * χ₁ = χ₁ * χ₂ from mul_comm _ _]
  ac_rfl

/--
@isnad1 id=eq.0h3v.s7.d5d52a2e8e8a from=translated src=- shape=c3888546 vocab=bde59374
-/
theorem quadraticProductCoefficients_eq_paired {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) :
    quadraticProductCoefficients χ₁ χ₂ = χ₁.zetaMul *
      (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) := by
  unfold quadraticProductCoefficients DirichletCharacter.zetaMul
  exact mul_assoc _ _ _

/-- An exact finite convolution identity: the other two character factors
are a pointwise twist of the first character's zeta convolution.
@isnad1 id=eq.0h4v.s8.fabfbe0e1597 from=translated src=- shape=1bd939a3 vocab=e8bf7b2a
-/
theorem character_pair_convolution_eq_twisted_zetaMul {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) (n : ℕ) :
    (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) n =
      χ₂ n * χ₁.zetaMul n := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply sum_congr rfl
  intro d hd
  obtain ⟨hprod, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hd
  have hm := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd
  have hk := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd
  rw [← hprod]
  simp only [toArithmeticFunction, coe_mk, hm, hk, ite_false, natCoe_apply,
    zeta_apply_ne hm, Nat.cast_one, one_mul, Nat.cast_mul, map_mul, MulChar.mul_apply]
  ring

/-- Nonnegative local factors give a nonnegative Dirichlet convolution at
every power of the same prime.
@isnad1 id=le.3h4v.s7.feec837596c3 from=translated src=- shape=b354370b vocab=211b70ba
-/
theorem arithmeticFunction_mul_prime_pow_nonneg (f g : ArithmeticFunction ℂ)
    {p : ℕ} (hp : p.Prime) (hf : ∀ k, 0 ≤ f (p ^ k)) (hg : ∀ k, 0 ≤ g (p ^ k))
    (k : ℕ) : 0 ≤ (f * g) (p ^ k) := by
  rw [ArithmeticFunction.mul_apply]
  apply sum_nonneg
  intro d hd
  obtain ⟨i, _, hi⟩ := (Nat.mem_divisors_prime_pow hp k).mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hd)
  obtain ⟨j, _, hj⟩ := (Nat.mem_divisors_prime_pow hp k).mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hd)
  rw [hi, hj]
  exact mul_nonneg (hf i) (hg j)

/-- The last convolution includes the endpoint divisor with complementary
factor one; all other local terms are nonnegative.
@isnad1 id=le.4h4v.s7.70cd248aaa94 from=translated src=- shape=2790e33c vocab=211b70ba
-/
theorem arithmeticFunction_le_mul_prime_pow (f g : ArithmeticFunction ℂ)
    {p : ℕ} (hp : p.Prime) (hf : ∀ k, 0 ≤ f (p ^ k)) (hg : ∀ k, 0 ≤ g (p ^ k))
    (hg1 : g 1 = 1) (k : ℕ) : f (p ^ k) ≤ (f * g) (p ^ k) := by
  rw [ArithmeticFunction.mul_apply]
  have hterm : f (p ^ k) * g 1 ≤
      ∑ d ∈ (p ^ k).divisorsAntidiagonal, f d.1 * g d.2 := by
    apply single_le_sum (f := fun d : ℕ × ℕ => f d.1 * g d.2)
      (s := (p ^ k).divisorsAntidiagonal) (a := (p ^ k, 1))
    · intro d hd
      obtain ⟨i, _, hi⟩ := (Nat.mem_divisors_prime_pow hp k).mp
        (Nat.fst_mem_divisors_of_mem_antidiagonal hd)
      obtain ⟨j, _, hj⟩ := (Nat.mem_divisors_prime_pow hp k).mp
        (Nat.snd_mem_divisors_of_mem_antidiagonal hd)
      rw [hi, hj]
      exact mul_nonneg (hf i) (hg j)
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one _, pow_ne_zero _ hp.ne_zero⟩
  simpa only [hg1, mul_one] using hterm

/--
@isnad1 id=le.3h5v.s8.2fb5382234af from=translated src=- shape=3e16d40f vocab=85190902
-/
theorem character_pair_prime_pow_nonneg_of_nonneg {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) (hχ₁ : χ₁ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (hχ₂p : 0 ≤ χ₂ p) (k : ℕ) :
    0 ≤ (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) (p ^ k) := by
  rw [character_pair_convolution_eq_twisted_zetaMul, Nat.cast_pow, map_pow]
  exact mul_nonneg (pow_nonneg hχ₂p _) (DirichletCharacter.zetaMul_prime_pow_nonneg hχ₁ hp k)

end TwinPrime.Analytic
