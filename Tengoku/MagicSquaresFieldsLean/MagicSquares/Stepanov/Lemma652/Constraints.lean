import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Unknowns
import Tengoku.Seed.Algebra.Polynomial.Degree.Lemmas
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# Turning the s_{t,n} identities into a finite homogeneous system

LN97 imposes `s_{t,n} = 0` by setting every coefficient of each
`s_{t,n}` equal to zero.  If all these polynomials have degree at most
`N`, the scalar equations are indexed by

    (t,n,l),  0 ≤ t < r, 0 ≤ n < M, 0 ≤ l ≤ N.

Hence the equation space has dimension exactly

    r M (N+1).

This file formalizes that coefficient-extraction step and the resulting
kernel argument.  It is the concrete finite-dimensional layer behind
the quantity `S` in equations (6.26)--(6.27).
-/

/-- Indices for all coefficient equations of the family `s_{t,n}`.-/
abbrev StepanovConstraintIndex (r M N : ℕ) :=
  Fin r × (Fin M × Fin (N + 1))

/-- Coordinate space of all scalar coefficient constraints.-/
abbrev StepanovConstraintSpace
    (F : Type*) (r M N : ℕ) :=
  StepanovConstraintIndex r M N → F

variable {F V : Type*}
  [Field F]
  [AddCommGroup V] [Module F V]

/-- Extract the first `N+1` coefficients from every polynomial in a
linear family `S(v)_{t,n}`.-/
noncomputable def polynomialFamilyCoeffConstraints
    {r M : ℕ}
    (N : ℕ)
    (S : V →ₗ[F] (Fin r → Fin M → Polynomial F)) :
    V →ₗ[F] StepanovConstraintSpace F r M N where
  toFun := fun v idx =>
    (S v idx.1 idx.2.1).coeff (idx.2.2 : ℕ)
  map_add' := by
    intro x y
    funext idx
    simp
  map_smul' := by
    intro a x
    funext idx
    simp

/--
@isnad1 id=eq.0h10v.s10.84529c61e5f2 from=translated src=- shape=1d5e49f0 vocab=dd7a4deb
-/
@[simp]
theorem polynomialFamilyCoeffConstraints_apply
    {r M N : ℕ}
    (S : V →ₗ[F] (Fin r → Fin M → Polynomial F))
    (v : V)
    (t : Fin r) (n : Fin M) (l : Fin (N + 1)) :
    polynomialFamilyCoeffConstraints N S v (t, (n, l))
      = (S v t n).coeff (l : ℕ) := by
  rfl

/-- A polynomial of degree at most `N` is zero if its first `N+1`
coefficients are all zero.
@isnad1 id=eq.2h3v.s7.71654bf2a2e8 from=translated src=- shape=caa489ee vocab=7a228405
-/
theorem polynomial_eq_zero_of_coeff_window_eq_zero
    (P : Polynomial F) (N : ℕ)
    (hdeg : P.natDegree ≤ N)
    (hcoeff : ∀ l : Fin (N + 1), P.coeff (l : ℕ) = 0) :
    P = 0 := by
  apply Polynomial.ext
  intro j
  simp only [Polynomial.coeff_zero]
  by_cases hj : j ≤ N
  · exact hcoeff ⟨j, Nat.lt_succ_of_le hj⟩
  · exact
      (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hdeg)
        j (Nat.lt_of_not_ge hj)

/-- Therefore vanishing of the scalar constraint vector forces all
`s_{t,n}` to vanish, provided their degree bound is known.
@isnad1 id=eq.2h9v.s10.94d6b593bc15 from=translated src=- shape=96ad2266 vocab=35015a2c
-/
theorem polynomialFamily_eq_zero_of_constraints_eq_zero
    {r M N : ℕ}
    (S : V →ₗ[F] (Fin r → Fin M → Polynomial F))
    (v : V)
    (hdeg : ∀ t n, (S v t n).natDegree ≤ N)
    (hz : polynomialFamilyCoeffConstraints N S v = 0) :
    ∀ t n, S v t n = 0 := by
  intro t n
  apply polynomial_eq_zero_of_coeff_window_eq_zero
    (S v t n) N (hdeg t n)
  intro l
  have h :=
    congrFun hz (t, (n, l))
  simpa using h

/-- The exact number of scalar coefficient constraints is
`r M (N+1)`.
@isnad1 id=eq.0h4v.s6.6ce41265a53e from=translated src=- shape=49c4cfcc vocab=cd8284fc
-/
theorem stepanovConstraintSpace_finrank
    (F : Type*) [Field F]
    (r M N : ℕ) :
    Module.finrank F (StepanovConstraintSpace F r M N)
      = r * M * (N + 1) := by
  change
    Module.finrank F
      (StepanovConstraintIndex r M N → F)
      = r * M * (N + 1)
  rw [Module.finrank_pi]
  simp [StepanovConstraintIndex, Nat.mul_assoc]

/-- Concrete `S < A` kernel theorem for the literal coefficient spaces
of Lemma 6.52.

The left side is the number of coefficient equations; the right side is
the number of scalar unknowns `e_{ij,l}`.
@isnad1 id=ex.1h8v.s9.51227fe6b0b9 from=translated src=- shape=c0b13883 vocab=080728ca
-/
theorem exists_nonzero_stepanovUnknown_in_kernel
    {m u D r M N : ℕ}
    (T :
      StepanovUnknowns F m u D →ₗ[F]
        StepanovConstraintSpace F r M N)
    (hcount :
      r * M * (N + 1) < m * (u + 1) * (D + 1)) :
    ∃ v : StepanovUnknowns F m u D,
      v ≠ 0 ∧ T v = 0 := by
  have hdim :
      Module.finrank F (StepanovConstraintSpace F r M N) <
        Module.finrank F (StepanovUnknowns F m u D) := by
    rw [stepanovConstraintSpace_finrank,
      stepanovUnknowns_finrank]
    exact hcount
  have hk :
      T.ker ≠
        (⊥ : Submodule F (StepanovUnknowns F m u D)) :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hk with
    ⟨v, hvker, hvne⟩
  refine ⟨v, hvne, ?_⟩
  simpa only [LinearMap.mem_ker] using hvker

end LN97
end MagicSquares
