import Tengoku.Jsp000570Lean.Erdos700.Bounds
import Tengoku.Jsp000570Lean.Erdos700.Arithmetic
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Legality of the four integer digit tables, and the uniform quotient range,
under the boundary condition c >= 3*b-a+1. The high digit of N/(p+b)
may be zero; only nonnegativity is required.
-/

namespace Erdos700.FourPrime.ParameterDigits

/-- Basic order and size consequences used by all four digit tables.
@isnad1 id=and.4h4v.s7.58d9d52fe90b from=translated src=- shape=3e89301d vocab=e94596d0
-/
theorem parameter_sizes (a b c p : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hp : 12 * c ^ 3 ≤ p) :
    0 < a ∧ 0 < b ∧ 9 ≤ c ∧ 0 < p ∧ a < c ∧ b < c ∧
      c ^ 3 < p ∧ 3 * c ^ 2 < p ∧ 3 * c < p := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hc9 : 9 ≤ c := by
    have h := Bounds.c_at_least_9 a b c ha hb hc
    omega
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hcc2 : c ≤ c ^ 2 := by
    nlinarith only [mul_nonneg (by omega : 0 ≤ c) (by omega : 0 ≤ c - 1)]
  obtain ⟨h3, h2, _⟩ := Bounds.large_base_thresholds c p hc2 hp
  have hc3 : 0 ≤ c ^ 3 := pow_nonneg (by omega : 0 ≤ c) 3
  have hab := Bounds.a_less_b a b c ha hb hc
  have hbc := Bounds.b_less_c a b c ha hb hc
  refine ⟨ha0, hb0, hc9, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith only [h3, h2, hc3, sq_nonneg c, hcc2, hab, hbc]

/-- Low, middle, and high digits of `N/p`.
@isnad1 id=and.4h4v.s8.85c9fb3d13ab from=translated src=- shape=70e32c83 vocab=e94596d0
-/
theorem digit_bounds_p (a b c p : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hp : 12 * c ^ 3 ≤ p) :
    0 ≤ a * b * c ∧ a * b * c < p ∧
      0 ≤ a * b + a * c + b * c ∧ a * b + a * c + b * c < p ∧
      0 ≤ a + b + c ∧ a + b + c < p := by
  obtain ⟨_, _, _, _, _, _, hc3, hc2, hcsmall⟩ := parameter_sizes a b c p ha hb hc hp
  have hZ0 := Bounds.Z_positive a b c ha hb hc
  have hZ3 := Bounds.Z_less_c_cubed a b c ha hb hc
  have hT0 := Bounds.T_positive a b c ha hb hc
  have hT2 := Bounds.T_less_3c_squared a b c ha hb hc
  have hS0 := Bounds.S_positive a b c ha hb hc
  have hS1 := Bounds.S_less_3c a b c ha hb hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith only [hc3, hc2, hcsmall, hZ0, hZ3, hT0, hT2, hS0, hS1]

/-- Low, middle, and high digits of `N/(p+a)`.
@isnad1 id=and.4h4v.s9.98945de843dc from=translated src=- shape=2c09cfa1 vocab=e94596d0
-/
theorem digit_bounds_a (a b c p : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hp : 12 * c ^ 3 ≤ p) :
    0 ≤ p + a - a * (b - a) * (c - a) ∧
      p + a - a * (b - a) * (c - a) < p + a ∧
      0 ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1 ∧
      b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1 < p + a ∧
      0 ≤ b + c - 3 * a ∧ b + c - 3 * a < p + a := by
  obtain ⟨ha0, _, hc9, _, _, hbc, hc3, hc2, hcsmall⟩ :=
    parameter_sizes a b c p ha hb hc hp
  have hA0 := Bounds.A_positive a b c ha hb hc
  have hA3 := Bounds.A_less_c_cubed a b c ha hb hc
  have hT0 := Bounds.T1_positive a b c ha hb hc
  have hTbc := Bounds.T1_less_than_bc a b c ha hb hc
  have hS0 := Bounds.S1_positive a b c ha hb hc
  have hS2 := Bounds.S1_less_2c a b c ha hb hc
  have hbc2 : b * c < c ^ 2 := by
    nlinarith only [mul_lt_mul_of_pos_right hbc (by omega : 0 < c)]
  have hTnonneg : 0 ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1 := by
    have : 0 < b * c - 2 * a * (b + c) + 3 * a ^ 2 := by
      nlinarith only [hT0]
    omega
  refine ⟨?_, ?_, hTnonneg, ?_, ?_, ?_⟩ <;>
    nlinarith only [ha0, hc9, hc3, hc2, hcsmall, hA0, hA3, hT0,
      hTbc, hS0, hS2, hbc2, sq_nonneg c]

/-- Low, middle, and high digits of `N/(p+b)`.
@isnad1 id=and.4h4v.s9.d4041d7821f8 from=translated src=- shape=9a9f7100 vocab=e94596d0
-/
theorem digit_bounds_b (a b c p : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hp : 12 * c ^ 3 ≤ p) :
    0 ≤ b * (b - a) * (c - b) ∧ b * (b - a) * (c - b) < p + b ∧
      0 ≤ p + b - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2) ∧
      p + b - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2) < p + b ∧
      0 ≤ a + c - 3 * b - 1 ∧ a + c - 3 * b - 1 < p + b := by
  obtain ⟨_, hb0, hc9, _, _, hbc, hc3, hc2, hcsmall⟩ :=
    parameter_sizes a b c p ha hb hc hp
  have hC0 := Bounds.C_positive a b c ha hb hc
  have hC3 := Bounds.C_less_c_cubed a b c ha hb hc
  have hB0 := Bounds.B_positive a b c ha hb hc
  have hBbc := Bounds.B_less_than_2bc a b c ha hb hc
  have hR0 := Bounds.R_at_least_one a b c ha hb hc
  have hRc := Bounds.R_less_than_c a b c ha hb hc
  have hbc2 : b * c < c ^ 2 := by
    nlinarith only [mul_lt_mul_of_pos_right hbc (by omega : 0 < c)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith only [hb0, hc9, hc3, hc2, hcsmall, hC0, hC3, hB0,
      hBbc, hR0, hRc, hbc2, sq_nonneg c]

/-- Low, middle, and high digits of `N/(p+c)`.
@isnad1 id=and.4h4v.s9.f27166a733a5 from=translated src=- shape=bf8d7d03 vocab=e94596d0
-/
theorem digit_bounds_c (a b c p : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hp : 12 * c ^ 3 ≤ p) :
    0 ≤ p + c - c * (c - a) * (c - b) ∧
      p + c - c * (c - a) * (c - b) < p + c ∧
      0 ≤ 3 * c ^ 2 - 2 * c * (a + b) + a * b - 1 ∧
      3 * c ^ 2 - 2 * c * (a + b) + a * b - 1 < p + c ∧
      0 ≤ p + c - (3 * c - a - b) ∧ p + c - (3 * c - a - b) < p + c := by
  obtain ⟨_, _, hc9, _, _, _, hc3, hc2, hcsmall⟩ :=
    parameter_sizes a b c p ha hb hc hp
  have hF0 := Bounds.F_positive a b c ha hb hc
  have hF3 := Bounds.F_less_c_cubed a b c ha hb hc
  have hU0 := Bounds.U_positive a b c ha hb hc
  have hU2 := Bounds.U_less_than_3c_squared a b c ha hb hc
  have hD0 := Bounds.D_positive a b c ha hb hc
  have hD3 := Bounds.D_less_3c a b c ha hb hc
  have hUnonneg : 0 ≤ 3 * c ^ 2 - 2 * c * (a + b) + a * b - 1 := by
    have : 0 < 3 * c ^ 2 - 2 * c * (a + b) + a * b := by
      nlinarith only [hU0]
    omega
  refine ⟨?_, ?_, hUnonneg, ?_, ?_, ?_⟩ <;>
    nlinarith only [hc9, hc3, hc2, hcsmall, hF0, hF3, hU0, hU2, hD0, hD3]

/-- A deliberately weaker threshold suffices for the fourth-power estimate.
@isnad1 id=lt.2h2v.s6.cf747c41081c from=translated src=- shape=cf83a6b4 vocab=971588f8
-/
theorem fourth_power_nearby (c p : ℤ) (hc : 0 < c) (hp : 10 * c ≤ p) :
    (p + c) ^ 4 < 2 * p ^ 4 := by
  let t := p - 10 * c
  have ht : 0 ≤ t := by dsimp [t]; omega
  have hid : 2 * p ^ 4 - (p + c) ^ 4 =
      t ^ 4 + 36 * c * t ^ 3 + 474 * c ^ 2 * t ^ 2 +
        2676 * c ^ 3 * t + 5359 * c ^ 4 := by
    dsimp [t]
    ring
  have hpos : 0 < 2 * p ^ 4 - (p + c) ^ 4 := by
    rw [hid]
    positivity
  linarith only [hpos]

/-- The product of the four bases is below `2*p^4`.
@isnad1 id=lt.4h4v.s7.c38e415d6074 from=translated src=- shape=53dc2fd8 vocab=e94596d0
-/
theorem product_lt_two_mul_p_four (a b c p : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hp : 12 * c ^ 3 ≤ p) :
    p * (p + a) * (p + b) * (p + c) < 2 * p ^ 4 := by
  obtain ⟨ha0, hb0, hc9, hp0, hac, hbc, _, _, _⟩ :=
    parameter_sizes a b c p ha hb hc hp
  have hc0 : 0 < c := by omega
  have hc3 : c ≤ c ^ 3 := by
    simpa using (pow_le_pow_right₀ (by omega : 1 ≤ c) (by decide : 1 ≤ 3))
  have hp10 : 10 * c ≤ p := by nlinarith only [hc3, hp, hc0]
  have hpc : 0 ≤ p + c := by omega
  have h01 : p * (p + a) ≤ (p + c) * (p + c) :=
    mul_le_mul (by omega) (by omega) (by omega) hpc
  have h012 : p * (p + a) * (p + b) ≤ (p + c) * (p + c) * (p + c) :=
    mul_le_mul h01 (by omega) (by omega) (mul_nonneg hpc hpc)
  have h0123 := mul_le_mul_of_nonneg_right h012 hpc
  have hprod : p * (p + a) * (p + b) * (p + c) ≤ (p + c) ^ 4 := by
    nlinarith only [h0123]
  exact lt_of_le_of_lt hprod (fourth_power_nearby c p hc0 hp10)

/-- A general integer quotient estimate from the product and half-range bounds.
Positivity of `k` is unnecessary for this upper bound.
@isnad1 id=lt.4h4v.s6.5ff743e9aab8 from=translated src=- shape=3a87a2a5 vocab=c3002787
-/
theorem quotient_lt_cube (N p k x : ℤ) (hp : 0 < p)
    (hN : N < 2 * p ^ 4) (hhalf : 2 * k ≤ N) (hpx : p ≤ x) :
    k / x < x ^ 3 := by
  have hx : 0 < x := lt_of_lt_of_le hp hpx
  have hpow : p ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (le_of_lt hp) hpx 4
  apply Int.ediv_lt_of_lt_mul hx
  nlinarith only [hN, hhalf, hpow]

/-- The quotient bound for any of the four bases, directly from the parameters.
@isnad1 id=lt.6h6v.s7.4adb144a1ae7 from=translated src=- shape=3cd217fb vocab=cb5d5132
-/
theorem parameter_quotient_lt_cube (a b c p k x : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hp : 12 * c ^ 3 ≤ p)
    (hhalf : 2 * k ≤ p * (p + a) * (p + b) * (p + c)) (hpx : p ≤ x) :
    k / x < x ^ 3 := by
  have hp0 := (parameter_sizes a b c p ha hb hc hp).2.2.2.1
  exact quotient_lt_cube _ p k x hp0
    (product_lt_two_mul_p_four a b c p ha hb hc hp) hhalf hpx

end Erdos700.FourPrime.ParameterDigits
