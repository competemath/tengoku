import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Invariant
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.Polynomial.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# LN97 Lemma 6.46: the root-of-unity orbit product

The middle of the proof on p. 302 forms

    ∏_{j=0}^{m-1} A(ζ^j Y),

where `ζ` is a primitive `m`th root of unity.

This file constructs that product directly and proves its invariance under
`Y ↦ ζY`.  Combined with `StepanovLemma646Invariant`, this shows that the
orbit product is a polynomial in `Y^m`, exactly the conclusion used by
LN97 before equation (6.19).
-/

/-- The `j`th factor in the root-of-unity orbit of `A`.-/
noncomputable def orbitFactor
    (ζ : F) (A : Polynomial F) (j : ℕ) : Polynomial F :=
  A.comp (C (ζ ^ j) * X)

/-- The product `∏_{j=0}^{m-1} A(ζ^j X)`.-/
noncomputable def orbitProduct
    (m : ℕ) (ζ : F) (A : Polynomial F) : Polynomial F :=
  ∏ j ∈ Finset.range m, orbitFactor ζ A j

@[simp]
theorem orbitFactor_zero (ζ : F) (A : Polynomial F) :
    orbitFactor ζ A 0 = A := by
  simp [orbitFactor]

/-- Composing one orbit factor with `X ↦ ζX` advances the exponent by one.-/
theorem orbitFactor_comp_scale
    (ζ : F) (A : Polynomial F) (j : ℕ) :
    (orbitFactor ζ A j).comp (C ζ * X) =
      orbitFactor ζ A (j + 1) := by
  simp [orbitFactor, Polynomial.comp_assoc, pow_succ]
  ring_nf

/-- The orbit is periodic after `m` steps when `ζ^m = 1`.-/
theorem orbitFactor_period
    {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (A : Polynomial F) :
    orbitFactor ζ A m = orbitFactor ζ A 0 := by
  simp [orbitFactor, hζ.pow_eq_one]

/-- A range product whose last value agrees with its first value is
unchanged by shifting all indices by one, provided the first value is
nonzero.-/
theorem prod_range_shift_eq
    {M : Type*} [CommMonoidWithZero M] [IsRightCancelMulZero M]
    (m : ℕ) (f : ℕ → M)
    (h0 : f 0 ≠ 0)
    (hperiod : f m = f 0) :
    (∏ j ∈ Finset.range m, f (j + 1)) =
      ∏ j ∈ Finset.range m, f j := by
  have hsucc := Finset.prod_range_succ f m
  have hsucc' := Finset.prod_range_succ' f m
  have hmul :
      (∏ j ∈ Finset.range m, f (j + 1)) * f 0 =
        (∏ j ∈ Finset.range m, f j) * f 0 := by
    calc
      (∏ j ∈ Finset.range m, f (j + 1)) * f 0 =
          ∏ j ∈ Finset.range (m + 1), f j := hsucc'.symm
      _ = (∏ j ∈ Finset.range m, f j) * f m := hsucc
      _ = (∏ j ∈ Finset.range m, f j) * f 0 := by rw [hperiod]
  exact mul_right_cancel₀ h0 hmul

/-- The orbit product is invariant under scaling the variable by a
primitive root of unity.-/
theorem orbitProduct_scale_invariant
    {m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ m)
    (A : Polynomial F) :
    (orbitProduct m ζ A).comp (C ζ * X) =
      orbitProduct m ζ A := by
  by_cases hA : A = 0
  · subst A
    simp [orbitProduct, orbitFactor]
  · rw [orbitProduct, Polynomial.prod_comp]
    have hshift :
        (∏ j ∈ Finset.range m, orbitFactor ζ A (j + 1)) =
          ∏ j ∈ Finset.range m, orbitFactor ζ A j := by
      apply prod_range_shift_eq
      · simpa using hA
      · exact orbitFactor_period (F := F) hζ A
    calc
      (∏ j ∈ Finset.range m,
          (orbitFactor ζ A j).comp (C ζ * X)) =
          ∏ j ∈ Finset.range m, orbitFactor ζ A (j + 1) := by
            apply Finset.prod_congr rfl
            intro j hj
            exact orbitFactor_comp_scale ζ A j
      _ = ∏ j ∈ Finset.range m, orbitFactor ζ A j := hshift

/-- Therefore the orbit product is a polynomial in `X^m`.-/
theorem orbitProduct_exists_comp_X_pow
    {m : ℕ} {ζ : F}
    (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m)
    (A : Polynomial F) :
    ∃ G : Polynomial F,
      orbitProduct m ζ A = G.comp (X ^ m) := by
  exact exists_comp_X_pow_of_primitiveRoot_scale_invariant
    (F := F) hm hζ (orbitProduct_scale_invariant (F := F) hζ A)

/-- A coarse degree estimate for the orbit product:
`deg orbitProduct ≤ m * deg A`.-/
theorem orbitProduct_natDegree_le
    (m : ℕ) (ζ : F) (A : Polynomial F) :
    (orbitProduct m ζ A).natDegree ≤ m * A.natDegree := by
  unfold orbitProduct
  calc
    (∏ j ∈ Finset.range m, orbitFactor ζ A j).natDegree
        ≤ ∑ j ∈ Finset.range m, (orbitFactor ζ A j).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.range m, A.natDegree := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (orbitFactor ζ A j).natDegree =
            (A.comp (C (ζ ^ j) * X)).natDegree := rfl
        _ ≤ A.natDegree * (C (ζ ^ j) * X).natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ A.natDegree * 1 := by
          apply Nat.mul_le_mul_left
          simpa using Polynomial.natDegree_C_mul_le (ζ ^ j) (X : Polynomial F)
        _ = A.natDegree := by simp
    _ = m * A.natDegree := by
      simp

end LN97
end MagicSquares
