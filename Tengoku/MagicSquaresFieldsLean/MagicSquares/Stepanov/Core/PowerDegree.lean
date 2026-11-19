import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.PowerFactor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace MagicSquares
namespace LN97

open Polynomial

variable {K : Type*} [Field K]

/-- The full natural-degree version of LN97 Corollary 6.49.

Assume `f` is nonconstant.  If `n ≤ t`, there is a polynomial `w₁`
such that

`E^(n)(w f^t) = w₁ f^(t-n)`

and

`natDegree w₁ ≤ natDegree w + n * (natDegree f - 1)`.

The nonconstant hypothesis is exactly what makes the book's expression
`deg f - 1` a natural number without ambiguity.-/
theorem ln97_6_49
    (w f : Polynomial K) (t n : ℕ)
    (hnt : n ≤ t)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree) :
    ∃ w₁ : Polynomial K,
      (hasseDeriv n) (w * f ^ t) = w₁ * f ^ (t - n) ∧
      w₁.natDegree ≤ w.natDegree + n * (f.natDegree - 1) := by
  obtain ⟨w₁, hw₁⟩ := ln97_6_49_factor w f t n hnt
  refine ⟨w₁, hw₁, ?_⟩

  by_cases hw₁zero : w₁ = 0
  · subst w₁
    simp

  have hfpow : f ^ (t - n) ≠ 0 :=
    pow_ne_zero _ hf

  have hderiv_ne :
      (hasseDeriv n) (w * f ^ t) ≠ 0 := by
    intro hz
    have hprod : w₁ * f ^ (t - n) = 0 := by
      rw [← hw₁]
      exact hz
    exact hw₁zero ((mul_eq_zero.mp hprod).resolve_right hfpow)

  have hw : w ≠ 0 := by
    intro hwzero
    apply hderiv_ne
    subst w
    simp

  have hbaseDegree :
      (w * f ^ t).natDegree =
        w.natDegree + t * f.natDegree := by
    rw [Polynomial.natDegree_mul hw (pow_ne_zero _ hf)]
    rw [Polynomial.natDegree_pow]

  have hfactorDegree :
      ((hasseDeriv n) (w * f ^ t)).natDegree =
        w₁.natDegree + (t - n) * f.natDegree := by
    rw [hw₁]
    rw [Polynomial.natDegree_mul hw₁zero hfpow]
    rw [Polynomial.natDegree_pow]

  have hderivDegree :=
    Polynomial.natDegree_hasseDeriv_le (w * f ^ t) n

  have hmain :
      w₁.natDegree + (t - n) * f.natDegree ≤
        w.natDegree + t * f.natDegree - n := by
    calc
      w₁.natDegree + (t - n) * f.natDegree =
          ((hasseDeriv n) (w * f ^ t)).natDegree := hfactorDegree.symm
      _ ≤ (w * f ^ t).natDegree - n := hderivDegree
      _ = w.natDegree + t * f.natDegree - n := by rw [hbaseDegree]

  -- Arithmetic normalization of the right-hand side:
  --
  --   deg w + t*deg f - n
  -- = (t-n)*deg f + (deg w + n*(deg f - 1)).
  have ht :
      t = (t - n) + n := by
    omega

  have hfd :
      f.natDegree = (f.natDegree - 1) + 1 := by
    omega

  have hnfd :
      n * f.natDegree =
        n * (f.natDegree - 1) + n := by
    calc
      n * f.natDegree =
          n * ((f.natDegree - 1) + 1) := by
            exact congrArg (fun d : ℕ => n * d) hfd
      _ = n * (f.natDegree - 1) + n := by
        rw [Nat.mul_add, Nat.mul_one]

  have hbeforeSub :
      w.natDegree + t * f.natDegree =
        n + ((t - n) * f.natDegree +
          (w.natDegree + n * (f.natDegree - 1))) := by
    calc
      w.natDegree + t * f.natDegree =
          w.natDegree + ((t - n) + n) * f.natDegree := by
            exact congrArg
              (fun s : ℕ => w.natDegree + s * f.natDegree) ht
      _ = w.natDegree +
          ((t - n) * f.natDegree + n * f.natDegree) := by
            rw [Nat.add_mul]
      _ = w.natDegree +
          ((t - n) * f.natDegree +
            (n * (f.natDegree - 1) + n)) := by
            rw [hnfd]
      _ = n + ((t - n) * f.natDegree +
          (w.natDegree + n * (f.natDegree - 1))) := by
            ac_rfl

  have hnormalized :
      w.natDegree + t * f.natDegree - n =
        (t - n) * f.natDegree +
          (w.natDegree + n * (f.natDegree - 1)) := by
    rw [hbeforeSub]
    omega

  rw [hnormalized] at hmain

  have hcancel :
      (t - n) * f.natDegree + w₁.natDegree ≤
        (t - n) * f.natDegree +
          (w.natDegree + n * (f.natDegree - 1)) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmain

  exact Nat.le_of_add_le_add_left hcancel

end LN97
end MagicSquares
