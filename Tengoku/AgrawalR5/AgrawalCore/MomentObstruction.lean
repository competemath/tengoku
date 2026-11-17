/-
The moment obstruction behind the local theory of Agrawal's congruence.

This file isolates the finite Fourier argument from all choices of
cyclotomic field and discrete logarithm.  The input is exactly the covariance
relation satisfied by those logarithms; the output is the equation cutting
out the possible residue classes.
-/
import Tengoku.Seed.Algebra.BigOperators.Field
import Tengoku.Seed.Algebra.GroupWithZero.Units.Fintype
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `j`-th weighted moment of a function on the units of a finite field.-/
def moment (e : Fˣ → F) (j : ℕ) : F :=
  ∑ a : Fˣ, (a : F) ^ j * e a

/-- Change of variables in the moment sum.

If `e (t*a) = t*e(a)`, then multiplication by `t` on the moment is the
same as multiplication by `t⁻ʲ`.
@isnad1 id=eq.1h4v.s8.33377e2cd141 from=translated src=- shape=332a170a vocab=d61875de
-/
theorem moment_covariance (e : Fˣ → F) (t : Fˣ) (j : ℕ)
    (hcov : ∀ a : Fˣ, (t : F) * e a = e (t * a)) :
    (t : F) * moment e j = ((t⁻¹ : Fˣ) : F) ^ j * moment e j := by
  unfold moment
  calc
    (t : F) * ∑ a : Fˣ, (a : F) ^ j * e a
        = ∑ a : Fˣ, (a : F) ^ j * e (t * a) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            rw [← hcov a]
            ring
    _ = ∑ b : Fˣ, (((t⁻¹ * b : Fˣ) : F) ^ j * e b) := by
          refine Fintype.sum_equiv (M := F) (Equiv.mulLeft t)
            (fun a : Fˣ ↦ (a : F) ^ j * e (t * a))
            (fun b : Fˣ ↦ (((t⁻¹ * b : Fˣ) : F) ^ j * e b)) fun a ↦ ?_
          simp
    _ = ((t⁻¹ : Fˣ) : F) ^ j * ∑ b : Fˣ, (b : F) ^ j * e b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          simp only [Units.val_mul, mul_pow]
          ring

/-- **Moment obstruction.**

Under the covariance relation, a nonzero `j`-th moment forces
`t^(j+1)=1`.  This is the algebraic heart of the inclusion
`im_r(S) ⊆ T` in the wider local theory.
@isnad1 id=eq.2h4v.s7.8f65c49823ce from=translated src=- shape=14bf1800 vocab=48941305
-/
theorem pow_succ_eq_one_of_moment_ne_zero (e : Fˣ → F) (t : Fˣ) (j : ℕ)
    (hcov : ∀ a : Fˣ, (t : F) * e a = e (t * a))
    (hM : moment e j ≠ 0) :
    (t : F) ^ (j + 1) = 1 := by
  have h :=
    moment_covariance e t j hcov
  have ht : (t : F) = ((t⁻¹ : Fˣ) : F) ^ j :=
    mul_right_cancel₀ hM h
  calc
    (t : F) ^ (j + 1) = (t : F) ^ j * (t : F) := pow_succ _ _
    _ = (t : F) ^ j * ((t⁻¹ : Fˣ) : F) ^ j := by rw [ht]
    _ = ((t : F) * ((t⁻¹ : Fˣ) : F)) ^ j := (mul_pow _ _ _).symm
    _ = 1 := by simp

/-- Factor form of the moment obstruction, valid without assuming that the
moment is nonzero.
@isnad1 id=eq.1h4v.s8.483733a6000b from=translated src=- shape=e7f85e65 vocab=d4bf57dd
-/
theorem moment_obstruction (e : Fˣ → F) (t : Fˣ) (j : ℕ)
    (hcov : ∀ a : Fˣ, (t : F) * e a = e (t * a)) :
    ((t : F) ^ (j + 1) - 1) * moment e j = 0 := by
  by_cases hM : moment e j = 0
  · simp [hM]
  · rw [pow_succ_eq_one_of_moment_ne_zero e t j hcov hM]
    simp

end AgrawalCore
