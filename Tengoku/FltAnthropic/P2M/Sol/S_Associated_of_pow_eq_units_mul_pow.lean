import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Associated_of_pow_eq_units_mul_pow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Associated_of_pow_eq_units_mul_pow

set_option autoImplicit false

/--
@isnad1 id=associat.2h5v.s6.ac77f09fdde4 from=translated src=- shape=b884d31e vocab=2783b609
-/
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a b : R) (n : ℕ) (hn : n ≠ 0) (u : Rˣ) (h : a ^ n = (u : R) * b ^ n) :
    Associated a b := by
  classical
  letI : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid

  have hassoc : Associated (a ^ n) (b ^ n) := ⟨u⁻¹, by
    rw [h, mul_comm ((u : R)) (b ^ n), mul_assoc, Units.mul_inv, mul_one]⟩
  by_cases ha : a = 0
  · subst ha
    have hb : b ^ n = 0 := by
      have := hassoc.symm
      rw [zero_pow hn] at this
      exact associated_zero_iff_eq_zero _ |>.mp this
    rw [pow_eq_zero_iff hn] at hb
    rw [hb]
  by_cases hb : b = 0
  · subst hb
    have : a ^ n = 0 := by
      rw [zero_pow hn] at hassoc
      exact associated_zero_iff_eq_zero _ |>.mp hassoc
    exact absurd ((pow_eq_zero_iff hn).mp this) ha
  have key := hassoc.normalizedFactors_eq
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, UniqueFactorizationMonoid.normalizedFactors_pow,
    nsmul_right_inj hn] at key
  exact (UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mpr key
