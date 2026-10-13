/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Orders in number fields

An order in a number field `K` is a subalgebra over `ℤ` that is finite as a `ℤ`-module and spans
`K` over `ℚ`.  The spanning condition ensures that `K` is the fraction field of the order; this
file installs that instance, so fractional ideals and Picard groups can be formed directly over an
order.

Every order consists of algebraic integers, because module-finiteness implies integrality.  Thus it
embeds canonically in the maximal order `𝓞 K`.  The maximal order itself is packaged as
`maximalNumberFieldOrder K`.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder`: an order in a number field.
* `TauCeti.GlobalNumberFields.maximalNumberFieldOrder`: the ring of integers as an order.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.isFractionRing`: the ambient number field is the
  fraction field of any order.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.le_ringOfIntegers`: every order is contained in the
  ring of integers.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

universe u

/-- An order in a number field `K`: a subring containing `ℤ`, finite as a `ℤ`-module, whose
`ℚ`-span is all of `K`. -/
structure NumberFieldOrder (K : Type u) [Field K] [NumberField K] where
  /-- The order as a `ℤ`-subalgebra of its ambient number field. -/
  toSubalgebra : Subalgebra ℤ K
  /-- An order is finitely generated as a `ℤ`-module. -/
  finite : Module.Finite ℤ toSubalgebra
  /-- An order has full rank in its ambient number field. -/
  spans : Submodule.span ℚ (toSubalgebra : Set K) = ⊤

namespace NumberFieldOrder

variable {K : Type u} [Field K] [NumberField K]

attribute [instance] finite

/-- Two orders in the same number field are equal when their underlying subalgebras are equal. -/
@[ext]
theorem ext {O O' : NumberFieldOrder K} (h : O.toSubalgebra = O'.toSubalgebra) : O = O' := by
  cases O
  cases O'
  cases h
  rfl

/-- Every element of an order is integral over `ℤ`. -/
theorem isIntegral (O : NumberFieldOrder K) (x : O.toSubalgebra) :
    IsIntegral ℤ (x : K) :=
  (IsIntegral.of_finite ℤ x).map O.toSubalgebra.val

/-- Every order in a number field is contained in its ring of integers. -/
theorem le_ringOfIntegers (O : NumberFieldOrder K) :
    O.toSubalgebra ≤ integralClosure ℤ K := fun x hx => by
  exact (O.isIntegral ⟨x, hx⟩)

end NumberFieldOrder

/-- The maximal order of a number field, namely its ring of integers. -/
def maximalNumberFieldOrder (K : Type u) [Field K] [NumberField K] : NumberFieldOrder K where
  toSubalgebra := integralClosure ℤ K
  finite := inferInstanceAs (Module.Finite ℤ (𝓞 K))
  spans := by
    apply top_unique
    rw [← (integralBasis K).span_eq]
    exact Submodule.span_mono fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      rw [integralBasis_apply]
      exact (RingOfIntegers.basis K i).property

@[simp]
theorem maximalNumberFieldOrder_toSubalgebra
    (K : Type u) [Field K] [NumberField K] :
    (maximalNumberFieldOrder K).toSubalgebra = integralClosure ℤ K := (rfl)

end TauCeti.GlobalNumberFields
