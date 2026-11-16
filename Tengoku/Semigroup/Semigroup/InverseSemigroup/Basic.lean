/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Tengoku.Seed.Algebra.Group.Idempotent
import Tengoku.Semigroup.Semigroup.InverseSemigroup.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inverse Semigroups: Basic Calculus

This file develops the basic calculus of inverse semigroups: involutivity of the
inverse, idempotency of `a * a⁻¹` and `a⁻¹ * a`, the fact that idempotents commute,
and the anti-homomorphism law `(a * b)⁻¹ = b⁻¹ * a⁻¹`. These are the lemmas needed
for the Vagner–Preston representation theorem
(`Semigroup.InverseSemigroup.VagnerPreston`) and for the natural partial order
(`Semigroup.InverseSemigroup.Order`).

## Main results

* `InverseSemigroup.inv_inv`: the inverse is involutive, `a⁻¹⁻¹ = a`.
* `InverseSemigroup.isIdempotentElem_mul_inv`, `InverseSemigroup.isIdempotentElem_inv_mul`:
  `a * a⁻¹` and `a⁻¹ * a` are idempotent.
* `InverseSemigroup.inv_idem`: an idempotent is its own inverse.
* `InverseSemigroup.isIdempotentElem_mul`: products of idempotents are idempotent.
* `InverseSemigroup.idempotent_mul_comm`: idempotents commute — the heart of the
  theory, equivalent to uniqueness of inverses.
* `InverseSemigroup.mul_inv_rev`: `(a * b)⁻¹ = b⁻¹ * a⁻¹`.
* `InverseSemigroup.isIdempotentElem_conj`: conjugates `a⁻¹ * e * a` of idempotents
  are idempotent.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995], Theorem 5.1.1.

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/
namespace Tengoku.Semigroup end Tengoku.Semigroup open Tengoku.Semigroup
namespace Tengoku.Semigroup.InverseSemigroup

variable {S : Type*} [InverseSemigroup S]

/-- The inverse is involutive.-/
@[simp] theorem inv_inv (a : S) : a⁻¹⁻¹ = a :=
  (inv_unique (inv_mul_inv a) (mul_inv_mul a)).symm

/-- `a * a⁻¹` is idempotent.-/
theorem isIdempotentElem_mul_inv (a : S) : IsIdempotentElem (a * a⁻¹) :=
  show a * a⁻¹ * (a * a⁻¹) = a * a⁻¹ by
    rw [← mul_assoc, mul_inv_mul]

/-- `a⁻¹ * a` is idempotent.-/
theorem isIdempotentElem_inv_mul (a : S) : IsIdempotentElem (a⁻¹ * a) :=
  show a⁻¹ * a * (a⁻¹ * a) = a⁻¹ * a by
    rw [← mul_assoc, inv_mul_inv]

/-- An idempotent is its own inverse.-/
theorem inv_idem {e : S} (he : IsIdempotentElem e) : e⁻¹ = e := by
  have h : e * e * e = e := by rw [he.eq, he.eq]
  exact (inv_unique h h).symm

/-- The product of two idempotents is idempotent (Howie, Thm 5.1.1, first
half): with `x := (e * f)⁻¹`, the element `f * x * e` is an idempotent
inverse of `e * f`, so `x = f * x * e` by uniqueness, `x` is idempotent, and
`e * f = x⁻¹ = x`.-/
theorem isIdempotentElem_mul {e f : S} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : IsIdempotentElem (e * f) := by
  obtain ⟨x, hx⟩ : ∃ x : S, x = (e * f)⁻¹ := ⟨_, rfl⟩
  have he2 : ∀ z : S, e * (e * z) = e * z := fun z => by rw [← mul_assoc, he.eq]
  have hf2 : ∀ z : S, f * (f * z) = f * z := fun z => by rw [← mul_assoc, hf.eq]
  have hx1 : (e * f) * x * (e * f) = e * f := by rw [hx]; exact mul_inv_mul (e * f)
  have hx2 : ∀ z : S, x * (e * (f * (x * z))) = x * z := fun z => by
    have h := congrArg (· * z) (inv_mul_inv (e * f))
    rw [← hx] at h
    simpa only [mul_assoc] using h
  -- `f * x * e` is an inverse of `e * f` ...
  have hA : (e * f) * (f * x * e) * (e * f) = e * f := by
    have h := hx1
    simp only [mul_assoc] at h ⊢
    rw [hf2, he2]
    exact h
  have hB : (f * x * e) * (e * f) * (f * x * e) = f * x * e := by
    simp only [mul_assoc]
    rw [he2, hf2, hx2]
  -- ... so it equals `x` by uniqueness, and hence `x` is idempotent
  have hxeq : f * x * e = x := (inv_unique hA hB).trans hx.symm
  have hxx : IsIdempotentElem x := by
    have h : (f * x * e) * (f * x * e) = f * x * e := by
      simp only [mul_assoc]
      rw [hx2]
    rw [hxeq] at h
    exact h
  -- finally `e * f = x⁻¹ = x` is idempotent
  have hef : e * f = x := by
    have h := inv_idem hxx
    rw [hx, inv_inv] at h
    rw [hx]
    exact h
  rw [hef]
  exact hxx

/-- **Idempotents commute.**  This is the crux of inverse semigroup theory:
a regular semigroup has unique inverses iff its idempotents commute.

Proof (Howie, Thm 5.1.1): both `e * f` and `f * e` are idempotent by
`isIdempotentElem_mul`, and each is then an inverse of the other, so
uniqueness gives `f * e = (e * f)⁻¹ = e * f`.-/
theorem idempotent_mul_comm {e f : S} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : e * f = f * e := by
  have hef := isIdempotentElem_mul he hf
  have hfe := isIdempotentElem_mul hf he
  have he2 : ∀ z : S, e * (e * z) = e * z := fun z => by rw [← mul_assoc, he.eq]
  have hf2 : ∀ z : S, f * (f * z) = f * z := fun z => by rw [← mul_assoc, hf.eq]
  have hA : (e * f) * (f * e) * (e * f) = e * f := by
    have h := hef.eq
    simp only [mul_assoc] at h ⊢
    rw [hf2, he2]
    exact h
  have hB : (f * e) * (e * f) * (f * e) = f * e := by
    have h := hfe.eq
    simp only [mul_assoc] at h ⊢
    rw [he2, hf2]
    exact h
  exact ((inv_unique hA hB).trans (inv_idem hef)).symm

/-- The inverse of a product: `b⁻¹ * a⁻¹` is an inverse of `a * b` (sliding
the idempotents `b * b⁻¹` and `a⁻¹ * a` past each other with
`idempotent_mul_comm`), so it is *the* inverse by `inv_unique`.-/
theorem mul_inv_rev (a b : S) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have hcomm := idempotent_mul_comm (isIdempotentElem_mul_inv b) (isIdempotentElem_inv_mul a)
  have h1 : (a * b) * (b⁻¹ * a⁻¹) * (a * b) = a * b :=
    calc (a * b) * (b⁻¹ * a⁻¹) * (a * b)
        = a * ((b * b⁻¹) * (a⁻¹ * a)) * b := by simp only [mul_assoc]
      _ = a * ((a⁻¹ * a) * (b * b⁻¹)) * b := by rw [hcomm]
      _ = (a * a⁻¹ * a) * (b * b⁻¹ * b) := by simp only [mul_assoc]
      _ = a * b := by rw [mul_inv_mul, mul_inv_mul]
  have h2 : (b⁻¹ * a⁻¹) * (a * b) * (b⁻¹ * a⁻¹) = b⁻¹ * a⁻¹ :=
    calc (b⁻¹ * a⁻¹) * (a * b) * (b⁻¹ * a⁻¹)
        = b⁻¹ * ((a⁻¹ * a) * (b * b⁻¹)) * a⁻¹ := by simp only [mul_assoc]
      _ = b⁻¹ * ((b * b⁻¹) * (a⁻¹ * a)) * a⁻¹ := by rw [← hcomm]
      _ = (b⁻¹ * b * b⁻¹) * (a⁻¹ * a * a⁻¹) := by simp only [mul_assoc]
      _ = b⁻¹ * a⁻¹ := by rw [inv_mul_inv, inv_mul_inv]
  exact (inv_unique h1 h2).symm

/-- Conjugating an idempotent: `a⁻¹ * e * a` is idempotent whenever `e` is
(expand the square and slide `e` past `a * a⁻¹` with
`idempotent_mul_comm`).-/
theorem isIdempotentElem_conj {e : S} (he : IsIdempotentElem e) (a : S) :
    IsIdempotentElem (a⁻¹ * (e * a)) := by
  have hcomm := idempotent_mul_comm (isIdempotentElem_mul_inv a) he
  change (a⁻¹ * (e * a)) * (a⁻¹ * (e * a)) = a⁻¹ * (e * a)
  calc (a⁻¹ * (e * a)) * (a⁻¹ * (e * a))
      = a⁻¹ * (e * (a * a⁻¹) * e) * a := by simp only [mul_assoc]
    _ = a⁻¹ * ((a * a⁻¹) * e * e) * a := by rw [← hcomm]
    _ = a⁻¹ * ((a * a⁻¹) * (e * e)) * a := by rw [mul_assoc (a * a⁻¹) e e]
    _ = a⁻¹ * ((a * a⁻¹) * e) * a := by rw [he.eq]
    _ = a⁻¹ * (e * (a * a⁻¹)) * a := by rw [hcomm]
    _ = a⁻¹ * (e * (a * a⁻¹ * a)) := by simp only [mul_assoc]
    _ = a⁻¹ * (e * a) := by rw [mul_inv_mul]

end Tengoku.Semigroup.InverseSemigroup
-- Tengoku: root names of this library moved to Tengoku.Semigroup so they do not collide with other libraries (generated)
