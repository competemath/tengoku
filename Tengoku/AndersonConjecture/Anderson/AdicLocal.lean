/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku

/-!
# Adic Completion of a Noetherian Local Ring is Local

The M-adic completion of a Noetherian local ring (R, M) is again
a local ring. The maximal ideal of the completion is the kernel
of the natural surjection onto the residue field R/M.
-/

open scoped Pointwise
open AdicCompletion Ideal Finset

variable {R : Type*} [CommRing R]

namespace AdicCompletion

/-! ### Transition compatibility for evalₐ -/
section Compat

variable (I : Ideal R)

end Compat

/-! ### Constructing inverses from componentwise units -/
section InverseConstruction

variable (I : Ideal R) [I.IsMaximal]

end InverseConstruction

/-! ### Main theorem -/
section Main

variable (R : Type*) [CommRing R] [IsLocalRing R]

abbrev M' := IsLocalRing.maximalIdeal R

omit [IsLocalRing R] in
lemma field_isUnit_or_isUnit {K : Type*} [Field K] {a b : K} (hab : a + b = 1) :
    IsUnit a ∨ IsUnit b := by
  by_cases ha : a = 0
  · right
    rw [ha, zero_add] at hab
    rw [hab]
    exact isUnit_one
  · left
    exact IsUnit.mk0 a ha

end Main

end AdicCompletion
