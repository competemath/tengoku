import Tengoku.Twinprime.TwinPrime.Analytic.CharacterCommonLevel
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionInducedValue
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionPeriodBound
import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticProductLSeries
import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticResidueComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Comparison with a fixed auxiliary quadratic character

Induction to the product of two distinct primitive conductors costs only
logarithms at one. Together with the actual four-factor residue estimate,
this compares a second L-value with a fixed auxiliary value. Any use of an
auxiliary zero is retained as an explicit hypothesis.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- The actual residue at the common product level is bounded by the two
original L-values and three logarithmic factors. The product character
is nonprincipal because the primitive conductors differ.-/
theorem norm_commonLevel_quadraticProduct_residue_le
    {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hq₀ : 1 < q₀) (hq : 1 < q) (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive)
    (hsq₀ : χ₀ ^ 2 = 1) (hne : q₀ ≠ q) :
    ‖regularizedQuadraticLFunctionProduct (commonLevelLeft χ₀ q)
      (commonLevelRight q₀ χ) 1‖ ≤
      5 * ‖DirichletCharacter.LFunction χ₀ 1‖ * ‖DirichletCharacter.LFunction χ 1‖ *
        (1 + Real.log (q₀ * q)) ^ 3 := by
  obtain ⟨hleft, hright⟩ := commonLevel_ne_one χ₀ χ hq₀ hq hχ₀ hχ
  have hχ₀' : χ₀ ≠ 1 := by
    intro heq
    apply hleft
    simp [commonLevelLeft, heq]
  have hχ' : χ ≠ 1 := by
    intro heq
    apply hright
    simp [commonLevelRight, heq]
  have hprod := commonLevel_mul_ne_one χ₀ χ hχ₀ hχ hsq₀ hne
  have hlog : 0 ≤ Real.log ((q₀ * q : ℕ) : ℝ) := Real.log_natCast_nonneg _
  simp only [Nat.cast_mul] at hlog
  have hleftBound : ‖DirichletCharacter.LFunction (commonLevelLeft χ₀ q) 1‖ ≤
      ‖DirichletCharacter.LFunction χ₀ 1‖ * (1 + Real.log (q₀ * q)) := by
    simpa only [commonLevelLeft, Nat.cast_mul] using
      norm_LFunction_changeLevel_one_le (Nat.dvd_mul_right q₀ q) χ₀ hχ₀'
  have hrightBound : ‖DirichletCharacter.LFunction (commonLevelRight q₀ χ) 1‖ ≤
      ‖DirichletCharacter.LFunction χ 1‖ * (1 + Real.log (q₀ * q)) := by
    simpa only [commonLevelRight, Nat.cast_mul] using
      norm_LFunction_changeLevel_one_le (Nat.dvd_mul_left q q₀) χ hχ'
  have hprodBound :
      ‖DirichletCharacter.LFunction (commonLevelLeft χ₀ q * commonLevelRight q₀ χ) 1‖ ≤
        5 * (1 + Real.log (q₀ * q)) := by
    have h := norm_LFunction_one_le_five_add_log
      (commonLevelLeft χ₀ q * commonLevelRight q₀ χ) hprod
    simp only [Nat.cast_mul] at h hlog
    linarith
  rw [regularizedQuadraticLFunctionProduct_one, norm_mul, norm_mul]
  calc
    _ ≤ (‖DirichletCharacter.LFunction χ₀ 1‖ * (1 + Real.log (q₀ * q))) *
        (‖DirichletCharacter.LFunction χ 1‖ * (1 + Real.log (q₀ * q))) *
          (5 * (1 + Real.log (q₀ * q))) := by
      gcongr
    _ = _ := by ring

/-- A zero of the auxiliary character remains an actual zero of the
four-factor product after induction to the common level.-/
theorem commonLevel_quadraticLFunctionProduct_eq_zero_of_auxiliary_zero
    {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1) (hzero : DirichletCharacter.LFunction χ₀ s = 0) :
    quadraticLFunctionProduct (commonLevelLeft χ₀ q) (commonLevelRight q₀ χ) s = 0 := by
  have hleft : DirichletCharacter.LFunction (commonLevelLeft χ₀ q) s = 0 :=
    LFunction_changeLevel_eq_zero_of_eq_zero (Nat.dvd_mul_right q₀ q) χ₀ s hs hzero
  simp only [quadraticLFunctionProduct, hleft, mul_zero, zero_mul]

end TwinPrime.Analytic
