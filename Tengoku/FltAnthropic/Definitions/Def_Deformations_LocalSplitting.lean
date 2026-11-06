import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Module

namespace TaylorWiles

variable {A : Type*} [CommRing A]

local notation "M₂ " A => Matrix (Fin 2) (Fin 2) A

structure IsEigenIdempotent (M : M₂ A) (a b : A) (e : M₂ A) : Prop where

  idem : e * e = e

  trace_eq_one : e.trace = 1

  mul_left : M * e = a • e

  mul_right : M * ((1 : M₂ A) - e) = b • ((1 : M₂ A) - e)

end TaylorWiles
