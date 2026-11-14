import Tengoku.Seed.NumberTheory.DirichletCharacter.Basic
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Primitive characters at a common product level

Induction to `q₀*q` preserves each primitive conductor and the square-one
identity. Different primitive levels therefore give distinct induced
characters. Their product is nonprincipal when the first is quadratic.
-/

noncomputable section

namespace TwinPrime.Analytic

def commonLevelLeft {q₀ : ℕ} (χ₀ : DirichletCharacter ℂ q₀) (q : ℕ) :
    DirichletCharacter ℂ (q₀ * q) :=
  χ₀.changeLevel (Nat.dvd_mul_right q₀ q)

def commonLevelRight (q₀ : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (q₀ * q) :=
  χ.changeLevel (Nat.dvd_mul_left q q₀)

theorem commonLevel_conductors {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive) :
    (commonLevelLeft χ₀ q).conductor = q₀ ∧
      (commonLevelRight q₀ χ).conductor = q := by
  constructor
  · exact (DirichletCharacter.conductor_changeLevel χ₀ (Nat.dvd_mul_right q₀ q)).trans hχ₀
  · exact (DirichletCharacter.conductor_changeLevel χ (Nat.dvd_mul_left q q₀)).trans hχ

theorem commonLevel_ne_one {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hq₀ : 1 < q₀) (hq : 1 < q) (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive) :
    commonLevelLeft χ₀ q ≠ 1 ∧ commonLevelRight q₀ χ ≠ 1 := by
  obtain ⟨hc₀, hc⟩ := commonLevel_conductors χ₀ χ hχ₀ hχ
  constructor
  · intro heq
    rw [heq, DirichletCharacter.conductor_one] at hc₀
    omega
  · intro heq
    rw [heq, DirichletCharacter.conductor_one] at hc
    omega

theorem commonLevel_sq_eq_one {q₀ q : ℕ}
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hχ₀ : χ₀ ^ 2 = 1) (hχ : χ ^ 2 = 1) :
    (commonLevelLeft χ₀ q) ^ 2 = 1 ∧ (commonLevelRight q₀ χ) ^ 2 = 1 := by
  constructor
  · change (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ q) χ₀) ^ 2 = 1
    rw [← map_pow, hχ₀, map_one]
  · change (DirichletCharacter.changeLevel (Nat.dvd_mul_left q q₀) χ) ^ 2 = 1
    rw [← map_pow, hχ, map_one]

theorem commonLevel_ne_of_primitive_levels_ne {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive) (hne : q₀ ≠ q) :
    commonLevelLeft χ₀ q ≠ commonLevelRight q₀ χ := by
  intro heq
  obtain ⟨hc₀, hc⟩ := commonLevel_conductors χ₀ χ hχ₀ hχ
  exact hne (hc₀.symm.trans ((congrArg DirichletCharacter.conductor heq).trans hc))

/-- Different primitive conductors prevent the product from becoming
principal. Only the first character needs the square-one hypothesis here.-/
theorem commonLevel_mul_ne_one {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive) (hsq₀ : χ₀ ^ 2 = 1) (hne : q₀ ≠ q) :
    commonLevelLeft χ₀ q * commonLevelRight q₀ χ ≠ 1 := by
  have hsq : (commonLevelLeft χ₀ q) ^ 2 = 1 := by
    change (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ q) χ₀) ^ 2 = 1
    rw [← map_pow, hsq₀, map_one]
  intro hmul
  have hinv : (commonLevelLeft χ₀ q)⁻¹ = commonLevelLeft χ₀ q :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq)
  exact commonLevel_ne_of_primitive_levels_ne χ₀ χ hχ₀ hχ hne
    (hinv.symm.trans (mul_eq_one_iff_inv_eq.mp hmul))

theorem commonLevel_mul_ne_one_of_lt {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive) (hsq₀ : χ₀ ^ 2 = 1) (hlt : q₀ < q) :
    commonLevelLeft χ₀ q * commonLevelRight q₀ χ ≠ 1 :=
  commonLevel_mul_ne_one χ₀ χ hχ₀ hχ hsq₀ hlt.ne

end TwinPrime.Analytic
