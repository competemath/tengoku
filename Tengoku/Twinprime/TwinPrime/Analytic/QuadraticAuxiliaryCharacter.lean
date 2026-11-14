import Tengoku.Seed.NumberTheory.LegendreSymbol.ZModChar
import Tengoku.Seed.NumberTheory.DirichletCharacter.Basic
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.IntervalCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A fixed primitive quadratic auxiliary character

The integer-valued character modulo four is transported to the complex
numbers. Its value at three rules out both proper divisor conductors.
All finite residue calculations are kernel-checked.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- The primitive odd quadratic character of conductor four, with complex values.-/
def auxiliaryQuadraticCharacter : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/--
@isnad1 id=eq.0h0v.s6.51587b15a6b8 from=translated src=- shape=966742d6 vocab=160948e1
-/
@[simp] theorem auxiliaryQuadraticCharacter_three :
    auxiliaryQuadraticCharacter (3 : ZMod 4) = -1 := by
  simp [auxiliaryQuadraticCharacter, ZMod.χ₄_apply]

/--
@isnad1 id=isquadra.0h0v.s4.9a453075aaf6 from=translated src=- shape=bfe16b09 vocab=d5255d2b
-/
theorem auxiliaryQuadraticCharacter_isQuadratic : auxiliaryQuadraticCharacter.IsQuadratic :=
  ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)

/--
@isnad1 id=eq.0h0v.s7.62e27df85fdc from=translated src=- shape=fce97d67 vocab=6fb24c1b
-/
theorem auxiliaryQuadraticCharacter_sq_eq_one : auxiliaryQuadraticCharacter ^ 2 = 1 :=
  auxiliaryQuadraticCharacter_isQuadratic.sq_eq_one

/--
@isnad1 id=ne.0h0v.s6.f1367dade768 from=translated src=- shape=3cd55e50 vocab=f0b94c4e
-/
theorem auxiliaryQuadraticCharacter_ne_one : auxiliaryQuadraticCharacter ≠ 1 := by
  intro h
  have hv := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) h
  rw [auxiliaryQuadraticCharacter_three,
    MulChar.one_apply (by decide : IsUnit (3 : ZMod 4))] at hv
  norm_num at hv

private theorem auxiliaryQuadraticCharacter_conductor_ne_two :
    auxiliaryQuadraticCharacter.conductor ≠ 2 := by
  intro hc
  have hcast : (3 : ZMod auxiliaryQuadraticCharacter.conductor) = 1 := by
    rw [hc]
    decide
  have hv := auxiliaryQuadraticCharacter.primitiveCharacter_apply_of_isCoprime
    (a := (3 : ℤ)) (show IsCoprime (3 : ℤ) (4 : ℤ) from
      (show Nat.Coprime 3 4 by decide).isCoprime)
  simp only [Int.cast_ofNat, hcast, map_one, auxiliaryQuadraticCharacter_three] at hv
  norm_num at hv

/--
@isnad1 id=eq.0h0v.s4.5461a73f9f10 from=translated src=- shape=12701c7e vocab=89abf0fb
-/
theorem auxiliaryQuadraticCharacter_conductor : auxiliaryQuadraticCharacter.conductor = 4 := by
  have hd : auxiliaryQuadraticCharacter.conductor ∣ 2 ^ 2 := by
    simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using
      auxiliaryQuadraticCharacter.conductor_dvd_level
  obtain ⟨k, hk, hconductor⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · have hc : auxiliaryQuadraticCharacter.conductor = 1 := by simpa using hconductor
    exact False.elim (auxiliaryQuadraticCharacter_ne_one
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc))
  · have hc : auxiliaryQuadraticCharacter.conductor = 2 := by simpa using hconductor
    exact False.elim (auxiliaryQuadraticCharacter_conductor_ne_two hc)
  · simpa using hconductor

/--
@isnad1 id=isprimit.0h0v.s3.0fee48020dc4 from=translated src=- shape=0792f4bc vocab=a06cc9ee
-/
theorem auxiliaryQuadraticCharacter_isPrimitive : auxiliaryQuadraticCharacter.IsPrimitive :=
  auxiliaryQuadraticCharacter_conductor

/-- A concrete witness for arguments requiring a primitive quadratic character.
@isnad1 id=ex.0h0v.s8.b62defcbc318 from=translated src=- shape=e4bf73c1 vocab=fe3a8499
-/
theorem exists_primitive_nonprincipal_quadratic_character :
    ∃ (q : ℕ) (_ : 1 < q) (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive ∧ χ ≠ 1 ∧ χ ^ 2 = 1 :=
  ⟨4, by norm_num, auxiliaryQuadraticCharacter, auxiliaryQuadraticCharacter_isPrimitive,
    auxiliaryQuadraticCharacter_ne_one, auxiliaryQuadraticCharacter_sq_eq_one⟩

end TwinPrime.Analytic
