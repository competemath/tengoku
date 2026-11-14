import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldDeletion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Frobenius factorization (2.17) and an exact-derivative certificate for the
reduction of the paper's rational function. All derivatives here are formal
polynomial derivatives in characteristic `p`.
-/

namespace PiIrrationality

noncomputable def deletionNumerator (p a b : ℕ) : Polynomial (ZMod p) :=
  Polynomial.C 5 * Polynomial.X ^ (2 * a) *
    (Polynomial.X ^ 4 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 25) ^ b

noncomputable def deletionDenominator (p c : ℕ) : Polynomial (ZMod p) :=
  (Polynomial.C 25 - Polynomial.X ^ 2) ^ (c + 1)

theorem deletionDenominator_ne_zero (p c : ℕ) [Fact p.Prime] :
    deletionDenominator p c ≠ 0 := by
  apply pow_ne_zero
  intro h
  have hc := congrArg (fun f : Polynomial (ZMod p) => f.coeff 2) h
  norm_num at hc

theorem deletionNumerator_frobenius (p a b : ℕ) [Fact p.Prime] :
    deletionNumerator p a b =
      (deletionNumerator p (a / p) (b / p)) ^ p * Polynomial.X ^ (2 * (a % p)) *
        (Polynomial.X ^ 4 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 25) ^
          (b % p) := by
  have ha : 2 * a = (2 * (a / p)) * p + 2 * (a % p) := by
    nlinarith [Nat.mod_add_div a p]
  have hb : b = (b / p) * p + b % p := by
    nlinarith [Nat.mod_add_div b p]
  have hfive : (Polynomial.C 5 : Polynomial (ZMod p)) ^ p = Polynomial.C 5 := by
    rw [← Polynomial.C_pow, ZMod.pow_card]
  unfold deletionNumerator
  rw [mul_pow, mul_pow, hfive, ← pow_mul, ← pow_mul]
  conv_lhs => rw [ha, hb, pow_add, pow_add]
  ring

theorem deletionDenominator_frobenius (p c : ℕ) [Fact p.Prime] :
    deletionDenominator p c *
        (Polynomial.C 25 - Polynomial.X ^ 2 : Polynomial (ZMod p)) ^ (p - 1 - c % p) =
      (deletionDenominator p (c / p)) ^ p := by
  have hc := Nat.mod_lt c (Fact.out : Nat.Prime p).pos
  have he : c + 1 + (p - 1 - c % p) = (c / p + 1) * p := by
    have hdecomp := Nat.mod_add_div c p
    nlinarith [show p - 1 - c % p + c % p + 1 = p by omega]
  unfold deletionDenominator
  rw [← pow_add, ← pow_mul, he]

theorem deletion_frobenius_cross_multiply (p a b c : ℕ) [Fact p.Prime] :
    deletionNumerator p a b * (deletionDenominator p (c / p)) ^ p =
      (deletionNumerator p (a / p) (b / p)) ^ p *
        evenLift p (finiteFieldH p (a % p) (b % p) (c % p)) *
          deletionDenominator p c := by
  rw [deletionNumerator_frobenius p a b, evenLift_finiteFieldH,
    ← deletionDenominator_frobenius]
  ring

noncomputable def finiteFieldRational (n p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
      (deletionNumerator p (1857 * n) (3714 * n)) /
    algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
      (deletionDenominator p (5570 * n))

theorem removablePrime_derivative_quotient {n p : ℕ} [Fact p.Prime]
    (hp : removablePrime n p) :
    ∃ N D : Polynomial (ZMod p), D ≠ 0 ∧ Polynomial.derivative D = 0 ∧
      finiteFieldRational n p =
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (Polynomial.derivative N) /
          algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) D := by
  let U := deletionNumerator p ((1857 * n) / p) ((3714 * n) / p)
  let V := evenPolynomialPrimitive p
    (finiteFieldH p ((1857 * n) % p) ((3714 * n) % p) ((5570 * n) % p))
  let D := (deletionDenominator p ((5570 * n) / p)) ^ p
  have hD : D ≠ 0 := pow_ne_zero _ (deletionDenominator_ne_zero p _)
  refine ⟨U ^ p * V, D, hD, derivative_pth_power_zmod p _, ?_⟩
  have hdV := removablePrime_primitive_derivative hp
  have hcross : deletionNumerator p (1857 * n) (3714 * n) * D =
      Polynomial.derivative (U ^ p * V) * deletionDenominator p (5570 * n) := by
    rw [← pth_power_mul_derivative_eq_derivative_mul, hdV]
    exact deletion_frobenius_cross_multiply p _ _ _
  unfold finiteFieldRational
  apply (div_eq_div_iff
    (RatFunc.algebraMap_ne_zero (deletionDenominator_ne_zero p _))
    (RatFunc.algebraMap_ne_zero hD)).2
  simpa only [map_mul] using congrArg
    (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))) hcross

end PiIrrationality
