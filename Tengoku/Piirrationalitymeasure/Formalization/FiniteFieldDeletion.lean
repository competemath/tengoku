import Tengoku.Piirrationalitymeasure.Formalization.FiniteField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The fractional-part condition selecting deleted primes implies that the
polynomial in (2.16), viewed in the variable `t`, has an antiderivative.
-/

namespace PiIrrationality

/--
@isnad1 id=eq.0h2v.s7.d45b61f63f82 from=translated src=- shape=a39f2bff vocab=8b48fb73
-/
theorem evenLift_eq_comp_X_sq (p : ℕ) (f : Polynomial (ZMod p)) :
    evenLift p f = f.comp (Polynomial.X ^ 2) := by
  conv_rhs => rw [f.as_sum_support]
  rw [Polynomial.sum_comp]
  unfold evenLift
  apply Finset.sum_congr rfl
  intro r hr
  rw [Polynomial.monomial_comp, ← pow_mul, Polynomial.C_mul_X_pow_eq_monomial]

/--
@isnad1 id=eq.0h4v.s10.27b53e0e74e0 from=translated src=- shape=0b0341fe vocab=50748f24
-/
theorem evenLift_finiteFieldH (p A B C : ℕ) :
    evenLift p (finiteFieldH p A B C) =
      Polynomial.X ^ (2 * A) *
        (Polynomial.X ^ 4 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 25) ^ B *
        (Polynomial.C 25 - Polynomial.X ^ 2) ^ (p - 1 - C) := by
  rw [evenLift_eq_comp_X_sq]
  simp [finiteFieldH, finiteFieldQuadratic, finiteFieldLinear,
    Polynomial.mul_comp, Polynomial.pow_comp, ← pow_mul]

/--
@isnad1 id=eq.0h3v.s6.c3e80bc2c920 from=translated src=- shape=d725a254 vocab=21b67143
-/
theorem fract_div_nat_add_eq_mod (m p : ℕ) (s : ℚ) :
    Int.fract ((m : ℚ) / p + s) = Int.fract ((m % p : ℕ) / (p : ℚ) + s) := by
  calc
    Int.fract ((m : ℚ) / p + s) =
        Int.fract ((m : ℚ) / p + s - (⌊(m : ℚ) / p⌋ : ℚ)) :=
      (Int.fract_sub_intCast _ _).symm
    _ = Int.fract (Int.fract ((m : ℚ) / p) + s) := by
      congr 1
      unfold Int.fract
      ring
    _ = _ := by rw [Int.fract_div_natCast_eq_div_natCast_mod]

/--
@isnad1 id=or.4h4v.s8.9e94bae9a09a from=translated src=- shape=3b9540c0 vocab=0b8dcf7b
-/
theorem deletion_residue_cases (p A B C : ℕ) (hp : 0 < p)
    (hodd : p % 2 = 1) (hAp : A < p)
    (hcond : Int.fract ((A : ℚ) / p + 1 / 2) + 2 * ((B : ℚ) / p) <
      (C : ℚ) / p) :
    (2 * A < p ∧ A + 2 * B + (p + 1) / 2 ≤ C) ∨
      (p + 1 ≤ 2 * A ∧ A + 2 * B ≤ C + (p - 1) / 2) := by
  have hpQ : 0 < (p : ℚ) := by exact_mod_cast hp
  have hApQ : (A : ℚ) < p := by exact_mod_cast hAp
  have hA0 : 0 ≤ (A : ℚ) / p := div_nonneg (Nat.cast_nonneg _) hpQ.le
  by_cases hlow : 2 * A < p
  · have hlowQ : 2 * (A : ℚ) < p := by exact_mod_cast hlow
    have hhalf : (A : ℚ) / p < 1 / 2 := by
      apply (div_lt_iff₀ hpQ).2
      linarith
    rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at hcond
    have hscaled := mul_lt_mul_of_pos_right hcond (show 0 < 2 * (p : ℚ) by positivity)
    have hleft : ((A : ℚ) / p + 1 / 2 + 2 * ((B : ℚ) / p)) * (2 * p) =
        2 * A + p + 4 * B := by field_simp; ring
    have hright : (C : ℚ) / p * (2 * p) = 2 * C := by field_simp
    rw [hleft, hright] at hscaled
    have hint : 2 * A + p + 4 * B < 2 * C := by exact_mod_cast hscaled
    exact Or.inl ⟨hlow, by omega⟩
  · have hhigh : p + 1 ≤ 2 * A := by omega
    have hhighQ : (p : ℚ) ≤ 2 * A := by exact_mod_cast (show p ≤ 2 * A by omega)
    have hhalf : (1 : ℚ) / 2 ≤ (A : ℚ) / p := by
      apply (le_div_iff₀ hpQ).2
      linarith
    have hlt : (A : ℚ) / p < 1 := (div_lt_one hpQ).2 hApQ
    have hfract : Int.fract ((A : ℚ) / p + 1 / 2) = (A : ℚ) / p - 1 / 2 := by
      calc
        _ = Int.fract ((A : ℚ) / p - 1 / 2 + 1) := by congr 1; ring
        _ = Int.fract ((A : ℚ) / p - 1 / 2) := Int.fract_add_one _
        _ = _ := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hfract] at hcond
    have hscaled := mul_lt_mul_of_pos_right hcond (show 0 < 2 * (p : ℚ) by positivity)
    have hleft : ((A : ℚ) / p - 1 / 2 + 2 * ((B : ℚ) / p)) * (2 * p) =
        2 * A - p + 4 * B := by field_simp; ring
    have hright : (C : ℚ) / p * (2 * p) = 2 * C := by field_simp
    rw [hleft, hright] at hscaled
    have hint : 2 * A + 4 * B < 2 * C + p := by
      exact_mod_cast (show 2 * (A : ℚ) + 4 * B < 2 * C + p by linarith)
    exact Or.inr ⟨hhigh, by omega⟩

/--
@isnad1 id=or.1h2v.s8.3c8857145f28 from=translated src=- shape=9efb7600 vocab=b1ebd29d
-/
theorem removablePrime_residue_cases {n p : ℕ} (hp : removablePrime n p) :
    (2 * ((1857 * n) % p) < p ∧
      (1857 * n) % p + 2 * ((3714 * n) % p) + (p + 1) / 2 ≤ (5570 * n) % p) ∨
    (p + 1 ≤ 2 * ((1857 * n) % p) ∧
      (1857 * n) % p + 2 * ((3714 * n) % p) ≤ (5570 * n) % p + (p - 1) / 2) := by
  have hcond := hp.2.2.2.2
  rw [fract_div_nat_add_eq_mod, Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod] at hcond
  have hp5 := hp.2.1
  have hodd : p % 2 = 1 := by
    rcases hp.1.eq_two_or_odd with htwo | hodd
    · omega
    · exact hodd
  exact deletion_residue_cases p _ _ _ hp.1.pos hodd (Nat.mod_lt _ hp.1.pos) hcond

/--
@isnad1 id=evenobst.1h2v.s6.1b409c9fb932 from=translated src=- shape=da0df0b4 vocab=66c1b46a
-/
theorem removablePrime_evenObstructionFree {n p : ℕ} [Fact p.Prime]
    (hp : removablePrime n p) :
    evenObstructionFree p
      (finiteFieldH p ((1857 * n) % p) ((3714 * n) % p) ((5570 * n) % p)) := by
  have hCp : (5570 * n) % p ≤ p - 1 := by
    have := Nat.mod_lt (5570 * n) hp.1.pos
    omega
  rcases removablePrime_residue_cases hp with ⟨_, hC⟩ | ⟨hA, hC⟩
  · exact finiteFieldH_evenObstructionFree_low_bound p _ _ _ hp.2.1 hCp hC
  · exact finiteFieldH_evenObstructionFree_high_bound p _ _ _ hp.2.1 hCp hA hC

/--
@isnad1 id=eq.1h2v.s9.a851eb33ff8c from=translated src=- shape=2a27cad5 vocab=36d9c6fc
-/
theorem removablePrime_primitive_derivative {n p : ℕ} [Fact p.Prime]
    (hp : removablePrime n p) :
    Polynomial.derivative (evenPolynomialPrimitive p
      (finiteFieldH p ((1857 * n) % p) ((3714 * n) % p) ((5570 * n) % p))) =
    evenLift p (finiteFieldH p ((1857 * n) % p) ((3714 * n) % p) ((5570 * n) % p)) :=
  evenPolynomialPrimitive_derivative p _ (removablePrime_evenObstructionFree hp)

/--
@isnad1 id=ex.1h2v.s11.ce3ad172a3ab from=translated src=- shape=f2584f01 vocab=4c5259fe
-/
theorem removablePrime_polynomial_primitive {n p : ℕ} [Fact p.Prime]
    (hp : removablePrime n p) :
    ∃ V : Polynomial (ZMod p), Polynomial.derivative V =
      Polynomial.X ^ (2 * ((1857 * n) % p)) *
        (Polynomial.X ^ 4 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 25) ^
          ((3714 * n) % p) *
        (Polynomial.C 25 - Polynomial.X ^ 2) ^ (p - 1 - (5570 * n) % p) := by
  refine ⟨evenPolynomialPrimitive p
    (finiteFieldH p ((1857 * n) % p) ((3714 * n) % p) ((5570 * n) % p)), ?_⟩
  rw [removablePrime_primitive_derivative hp, evenLift_finiteFieldH]

end PiIrrationality
