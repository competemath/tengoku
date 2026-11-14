import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionInducedValue
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterCommonLevel
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionRealSign

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transporting a primitive quadratic zero exclusion

The conductor of a nonprincipal character is greater than one, and its
primitive character remains quadratic. The exact Euler multiplier has no
zeros in the positive half-plane. Consequently an explicitly supplied
primitive real zero exclusion transfers to every nonprincipal quadratic
character. No zero-free interval or uniform value estimate is asserted here.
-/

noncomputable section

namespace TwinPrime.Analytic

local instance {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

theorem one_lt_conductor_of_ne_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 1 < χ.conductor := by
  have hpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hne : χ.conductor ≠ 1 := fun h =>
    hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  omega

theorem primitiveCharacter_sq_eq_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    χ.primitiveCharacter ^ 2 = 1 := by
  apply DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
  rw [map_pow, χ.changeLevel_primitiveCharacter, map_one, hsq]

/-- The actual zeros agree with those of the primitive inducing character
in the positive half-plane, away from the possible principal pole.-/
theorem LFunction_eq_zero_iff_primitiveCharacter_of_re_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1) (hre : 0 < s.re) :
    DirichletCharacter.LFunction χ s = 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [χ.changeLevel_primitiveCharacter] using
    LFunction_changeLevel_eq_zero_iff_of_re_pos
      χ.conductor_dvd_level χ.primitiveCharacter s hs hre

/-- A globally supplied primitive quadratic zero exclusion on `[σ,1)`
also excludes zeros of every nonprincipal quadratic character there.-/
theorem LFunction_nonprincipal_quadratic_ne_zero_of_primitive_interval
    (σ : ℝ) (hσ : 0 < σ)
    (hno : ∀ (r : ℕ) [NeZero r], 1 < r →
      ∀ ψ : DirichletCharacter ℂ r, ψ.IsPrimitive → ψ ^ 2 = 1 →
      ∀ u : ℝ, u ∈ Set.Ico σ 1 → DirichletCharacter.LFunction ψ (u : ℂ) ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1)
    (u : ℝ) (hu : u ∈ Set.Ico σ 1) :
    DirichletCharacter.LFunction χ (u : ℂ) ≠ 0 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := hno χ.conductor (one_lt_conductor_of_ne_one χ hχ)
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
    (primitiveCharacter_sq_eq_one χ hsq) u hu
  have hu1 : (u : ℂ) ≠ 1 := by exact_mod_cast ne_of_lt hu.2
  have hu0 : 0 < (u : ℂ).re := hσ.trans_le hu.1
  exact fun hz => hprim
    ((LFunction_eq_zero_iff_primitiveCharacter_of_re_pos χ (u : ℂ) hu1 hu0).mp hz)

/-- At a common product level, distinct primitive quadratic conductors
give three nonprincipal factors. A primitive zero exclusion therefore
supplies all three interval hypotheses in the actual product sign theorem.-/
theorem commonLevel_quadraticLFunctionProduct_re_neg_of_primitive_interval
    (σ : ℝ) (hσ : 19 / 20 ≤ σ) (hσ1 : σ < 1)
    (hno : ∀ (r : ℕ) [NeZero r], 1 < r →
      ∀ ψ : DirichletCharacter ℂ r, ψ.IsPrimitive → ψ ^ 2 = 1 →
      ∀ u : ℝ, u ∈ Set.Ico σ 1 → DirichletCharacter.LFunction ψ (u : ℂ) ≠ 0)
    {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hq₀ : 1 < q₀) (hq : 1 < q) (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive)
    (hsq₀ : χ₀ ^ 2 = 1) (hsq : χ ^ 2 = 1) (hne : q₀ ≠ q) :
    (quadraticLFunctionProduct (commonLevelLeft χ₀ q)
      (commonLevelRight q₀ χ) (σ : ℂ)).re < 0 := by
  have hσ0 : 0 < σ := by linarith
  obtain ⟨hleft, hright⟩ := commonLevel_ne_one χ₀ χ hq₀ hq hχ₀ hχ
  obtain ⟨hsqleft, hsqright⟩ := commonLevel_sq_eq_one χ₀ χ hsq₀ hsq
  have hprod := commonLevel_mul_ne_one χ₀ χ hχ₀ hχ hsq₀ hne
  have hsqprod : (commonLevelLeft χ₀ q * commonLevelRight q₀ χ) ^ 2 = 1 := by
    rw [mul_pow, hsqleft, hsqright, mul_one]
  apply quadraticLFunctionProduct_real_re_neg_of_no_zeros
    (commonLevelLeft χ₀ q) (commonLevelRight q₀ χ)
    hleft hright hprod hsqleft hsqright σ hσ hσ1
  · exact LFunction_nonprincipal_quadratic_ne_zero_of_primitive_interval
      σ hσ0 hno _ hleft hsqleft
  · exact LFunction_nonprincipal_quadratic_ne_zero_of_primitive_interval
      σ hσ0 hno _ hright hsqright
  · exact LFunction_nonprincipal_quadratic_ne_zero_of_primitive_interval
      σ hσ0 hno _ hprod hsqprod

end TwinPrime.Analytic
