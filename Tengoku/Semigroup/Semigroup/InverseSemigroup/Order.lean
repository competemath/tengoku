/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Tengoku.Seed.Order.Defs.PartialOrder
import Tengoku.Semigroup.Semigroup.InverseSemigroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inverse Semigroups: the Natural Partial Order

This file defines the natural partial order on an inverse semigroup,
`a ≤ b ↔ a = a * a⁻¹ * b`, and develops its basic calculus: the equivalent
characterizations (`a` is an idempotent left multiple of `b`, an idempotent
right multiple of `b`, or equals `b * (a⁻¹ * a)`), antisymmetry and
transitivity, and compatibility with multiplication and inversion.

## Main definitions

* `InverseSemigroup.instPartialOrder`: the natural partial order on an inverse
  semigroup, `a ≤ b ↔ a = a * a⁻¹ * b`.

## Main results

* `InverseSemigroup.le_def`: unfolding lemma, `a ≤ b ↔ a = a * a⁻¹ * b`.
* `InverseSemigroup.le_iff_exists_idem_mul`, `InverseSemigroup.le_iff_exists_mul_idem`:
  `a ≤ b` iff `a = e * b` (resp. `a = b * f`) for some idempotent `e` (resp. `f`).
* `InverseSemigroup.le_iff_eq_mul_inv_mul`: the mirror characterization
  `a ≤ b ↔ a = b * (a⁻¹ * a)`.
* `InverseSemigroup.mul_le_mul`: the order is compatible with multiplication.
* `InverseSemigroup.inv_le_inv_iff`: the order is compatible with inversion.
* `InverseSemigroup.le_iff_eq_mul`: on an idempotent `e`, the order reduces to
  `e ≤ b ↔ e = e * b`.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/
namespace Tengoku.Semigroup end Tengoku.Semigroup open Tengoku.Semigroup
namespace Tengoku.Semigroup.InverseSemigroup

variable {S : Type*} [InverseSemigroup S]

/-! ### Auxiliary lemmas on the defining equation

These raw forms of the characterization lemmas are phrased without `≤` so they
can be used to build the `PartialOrder` instance; the public versions in terms
of `≤` follow the instance. -/

/-- If `a = e * b` with `e` idempotent, then `a = a * a⁻¹ * b`: the defining
equation of the natural partial order only needs *some* idempotent witness.-/
private theorem eq_idem_mul_aux {a b e : S} (he : IsIdempotentElem e) (hae : a = e * b) :
    a = a * a⁻¹ * b := by
  have hinv : a⁻¹ = b⁻¹ * e := by rw [hae, mul_inv_rev, inv_idem he]
  rw [hinv, hae]
  calc e * b
      = e * e * (b * b⁻¹ * b) := by rw [he.eq, mul_inv_mul]
    _ = e * (e * (b * b⁻¹)) * b := by simp only [mul_assoc]
    _ = e * (b * b⁻¹ * e) * b := by rw [idempotent_mul_comm he (isIdempotentElem_mul_inv b)]
    _ = e * b * (b⁻¹ * e) * b := by simp only [mul_assoc]

/-- From `a = a * a⁻¹ * b` derive the mirror equation `a = b * (a⁻¹ * a)`
(slide the idempotents `a * a⁻¹` and `b * b⁻¹` past each other).-/
private theorem eq_mul_inv_mul_aux {a b : S} (hab : a = a * a⁻¹ * b) :
    a = b * (a⁻¹ * a) := by
  have hinv : a⁻¹ = b⁻¹ * (a * a⁻¹) := by
    conv_lhs => rw [hab]
    rw [mul_inv_rev, inv_idem (isIdempotentElem_mul_inv a)]
  have hcomm := idempotent_mul_comm (isIdempotentElem_mul_inv b) (isIdempotentElem_mul_inv a)
  symm
  calc b * (a⁻¹ * a)
      = b * (b⁻¹ * (a * a⁻¹) * a) := by conv_lhs => rw [hinv]
    _ = b * b⁻¹ * (a * a⁻¹ * a) := by simp only [mul_assoc]
    _ = b * b⁻¹ * a := by rw [mul_inv_mul]
    _ = b * b⁻¹ * (a * a⁻¹ * b) := by conv_lhs => rw [hab]
    _ = b * b⁻¹ * (a * a⁻¹) * b := by simp only [mul_assoc]
    _ = a * a⁻¹ * (b * b⁻¹) * b := by rw [hcomm]
    _ = a * a⁻¹ * (b * b⁻¹ * b) := by simp only [mul_assoc]
    _ = a * a⁻¹ * b := by rw [mul_inv_mul]
    _ = a := hab.symm

/-- Transitivity of the defining equation: the composite idempotent witness is
`(a * a⁻¹) * (b * b⁻¹)`.-/
private theorem le_trans_aux {a b c : S} (hab : a = a * a⁻¹ * b) (hbc : b = b * b⁻¹ * c) :
    a = a * a⁻¹ * c := by
  have he : IsIdempotentElem (a * a⁻¹ * (b * b⁻¹)) :=
    isIdempotentElem_mul (isIdempotentElem_mul_inv a) (isIdempotentElem_mul_inv b)
  refine eq_idem_mul_aux he ?_
  calc a = a * a⁻¹ * b := hab
    _ = a * a⁻¹ * (b * b⁻¹ * c) := by rw [← hbc]
    _ = a * a⁻¹ * (b * b⁻¹) * c := by simp only [mul_assoc]

/-- Antisymmetry of the defining equation.-/
private theorem le_antisymm_aux {a b : S} (hab : a = a * a⁻¹ * b) (hba : b = b * b⁻¹ * a) :
    a = b :=
  calc a = b * (a⁻¹ * a) := eq_mul_inv_mul_aux hab
    _ = b * b⁻¹ * a * (a⁻¹ * a) := by conv_lhs => rw [hba]
    _ = b * b⁻¹ * (a * a⁻¹ * a) := by simp only [mul_assoc]
    _ = b * b⁻¹ * a := by rw [mul_inv_mul]
    _ = b := hba.symm

/-! ### The partial order -/

/-- The **natural partial order** on an inverse semigroup: `a ≤ b` iff
`a = a * a⁻¹ * b`, i.e. `a` is an idempotent multiple of `b`.-/
instance : PartialOrder S where
  le a b := a = a * a⁻¹ * b
  le_refl a := (mul_inv_mul a).symm
  le_trans _ _ _ := le_trans_aux
  le_antisymm _ _ := le_antisymm_aux

/-- Unfolding lemma for the natural partial order: `a ≤ b ↔ a = a * a⁻¹ * b`.
@isnad1 id=iff.0h3v.s5.192a983bae78 from=translated src=- shape=81826700 vocab=7d87b604
-/
theorem le_def {a b : S} : a ≤ b ↔ a = a * a⁻¹ * b := Iff.rfl

/-- `a ≤ b` iff `a` is an idempotent *left* multiple of `b`.
@isnad1 id=iff.0h3v.s5.14eb91d423fd from=translated src=- shape=a8550db2 vocab=4e70d85b
-/
theorem le_iff_exists_idem_mul {a b : S} :
    a ≤ b ↔ ∃ e : S, IsIdempotentElem e ∧ a = e * b :=
  ⟨fun h => ⟨a * a⁻¹, isIdempotentElem_mul_inv a, le_def.mp h⟩,
   fun ⟨_, he, hae⟩ => le_def.mpr (eq_idem_mul_aux he hae)⟩

/-- If `a ≤ b` then `a = b * (a⁻¹ * a)`: below an element, the left form of the
defining equation can be traded for the mirror right form.-/
theorem eq_mul_inv_mul_of_le {a b : S} (h : a ≤ b) : a = b * (a⁻¹ * a) :=
  eq_mul_inv_mul_aux (le_def.mp h)

/-- An idempotent *right* multiple lies below: if `a = b * f` with `f`
idempotent then `a ≤ b` (conjugate the idempotent to the other side,
`a = (b * f * b⁻¹) * b`).
@isnad1 id=le.2h4v.s5.02b0875012fe from=translated src=- shape=58d57b01 vocab=4e70d85b
-/
theorem le_of_eq_mul_idem {a b f : S} (hf : IsIdempotentElem f) (hab : a = b * f) :
    a ≤ b := by
  rw [le_iff_exists_idem_mul]
  refine ⟨b * (f * b⁻¹), by simpa only [inv_inv] using isIdempotentElem_conj hf b⁻¹, ?_⟩
  have hcomm := idempotent_mul_comm hf (isIdempotentElem_inv_mul b)
  calc a = b * f := hab
    _ = b * b⁻¹ * b * f := by rw [mul_inv_mul]
    _ = b * (b⁻¹ * b * f) := by simp only [mul_assoc]
    _ = b * (f * (b⁻¹ * b)) := by rw [← hcomm]
    _ = b * (f * b⁻¹) * b := by simp only [mul_assoc]

/-- The mirror characterization of the natural partial order:
`a ≤ b ↔ a = b * (a⁻¹ * a)`.
@isnad1 id=iff.0h3v.s5.4dcb41d9ff8e from=translated src=- shape=b47535e4 vocab=7d87b604
-/
theorem le_iff_eq_mul_inv_mul {a b : S} : a ≤ b ↔ a = b * (a⁻¹ * a) :=
  ⟨eq_mul_inv_mul_of_le, le_of_eq_mul_idem (isIdempotentElem_inv_mul a)⟩

/-- `a ≤ b` iff `a` is an idempotent *right* multiple of `b`.
@isnad1 id=iff.0h3v.s5.2b3836377f8a from=translated src=- shape=83183418 vocab=4e70d85b
-/
theorem le_iff_exists_mul_idem {a b : S} :
    a ≤ b ↔ ∃ f : S, IsIdempotentElem f ∧ a = b * f :=
  ⟨fun h => ⟨a⁻¹ * a, isIdempotentElem_inv_mul a, eq_mul_inv_mul_of_le h⟩,
   fun ⟨_, hf, hab⟩ => le_of_eq_mul_idem hf hab⟩

/-! ### Compatibility with the operations -/

/-- The natural partial order is compatible with inversion.
@isnad1 id=le.1h3v.s5.1c375cdf9bcd from=translated src=- shape=508d89c6 vocab=9624b6d8
-/
protected theorem inv_le_inv {a b : S} (h : a ≤ b) : a⁻¹ ≤ b⁻¹ := by
  obtain ⟨e, he, hae⟩ := le_iff_exists_idem_mul.mp h
  exact le_of_eq_mul_idem he (by rw [hae, mul_inv_rev, inv_idem he])

/-- Inversion is an order embedding of the natural partial order into itself.
@isnad1 id=iff.0h3v.s5.6669a67593b5 from=translated src=- shape=f432663e vocab=9624b6d8
-/
@[simp] protected theorem inv_le_inv_iff {a b : S} : a⁻¹ ≤ b⁻¹ ↔ a ≤ b :=
  ⟨fun h => by simpa only [inv_inv] using InverseSemigroup.inv_le_inv h,
   InverseSemigroup.inv_le_inv⟩

/-- The natural partial order is compatible with multiplication.
@isnad1 id=le.2h5v.s6.9b9f73b52d35 from=translated src=- shape=64d2154e vocab=b8ef965a
-/
protected theorem mul_le_mul {a b c d : S} (hab : a ≤ b) (hcd : c ≤ d) :
    a * c ≤ b * d := by
  obtain ⟨e, he, hae⟩ := le_iff_exists_idem_mul.mp hab
  obtain ⟨f, hf, hcf⟩ := le_iff_exists_idem_mul.mp hcd
  have hcomm := idempotent_mul_comm hf (isIdempotentElem_inv_mul b)
  refine le_iff_exists_idem_mul.mpr ⟨e * (b * (f * b⁻¹)),
    isIdempotentElem_mul he (by simpa only [inv_inv] using isIdempotentElem_conj hf b⁻¹), ?_⟩
  symm
  calc e * (b * (f * b⁻¹)) * (b * d)
      = e * (b * (f * (b⁻¹ * b)) * d) := by simp only [mul_assoc]
    _ = e * (b * (b⁻¹ * b * f) * d) := by rw [hcomm]
    _ = e * (b * b⁻¹ * b * (f * d)) := by simp only [mul_assoc]
    _ = e * (b * (f * d)) := by rw [mul_inv_mul]
    _ = a * c := by rw [hae, hcf, mul_assoc]

/-! ### Idempotents -/

/-- On an idempotent `e`, the natural partial order reduces to absorption:
`e ≤ b ↔ e = e * b`.
@isnad1 id=iff.1h3v.s5.c6ea2ad26122 from=translated src=- shape=ffaedafd vocab=4e70d85b
-/
theorem le_iff_eq_mul {e b : S} (he : IsIdempotentElem e) : e ≤ b ↔ e = e * b := by
  rw [le_def, inv_idem he, he.eq]

/-- Multiplying by an idempotent on the right moves down: `a * f ≤ a`.
@isnad1 id=le.1h3v.s5.f7f502a58ea1 from=translated src=- shape=d789f8bf vocab=4e70d85b
-/
theorem mul_le_left {a f : S} (hf : IsIdempotentElem f) : a * f ≤ a :=
  le_of_eq_mul_idem hf rfl

/-- Multiplying by an idempotent on the left moves down: `e * b ≤ b`.
@isnad1 id=le.1h3v.s5.2901131bb47a from=translated src=- shape=691cd105 vocab=4e70d85b
-/
theorem mul_le_right {e b : S} (he : IsIdempotentElem e) : e * b ≤ b :=
  le_iff_exists_idem_mul.mpr ⟨e, he, rfl⟩

end Tengoku.Semigroup.InverseSemigroup
-- Tengoku: root names of this library moved to Tengoku.Semigroup so they do not collide with other libraries (generated)
