import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

variable (W : Affine F) in

class GenusOnePlaceGate : Type u where

  pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField

  deg_eq_one : ∀ v : AlgebraicCurve.Place F W.FunctionField, v.deg = 1

variable {W : Affine F} [GenusOnePlaceGate W]

abbrev pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  GenusOnePlaceGate.pointEquivPlace (W := W)

def placeOfPoint : W.Point → AlgebraicCurve.Place F W.FunctionField :=
  pointEquivPlace (W := W)

/--
@isnad1 id=eq.0h3v.s8.d4dbb0bfc054 from=translated src=- shape=0c3493f6 vocab=ee6c70a5
-/
theorem deg_eq_one (v : AlgebraicCurve.Place F W.FunctionField) : v.deg = 1 :=
  GenusOnePlaceGate.deg_eq_one v

def divisorSum : AlgebraicCurve.Divisor F W.FunctionField →+ W.Point :=
  Finsupp.liftAddHom fun v => zmultiplesHom W.Point ((pointEquivPlace (W := W)).symm v)

variable (W) in

class AbelTheorem : Prop where

  isPrincipal_iff_divisorSum_eq_zero :
    ∀ D : AlgebraicCurve.Divisor F W.FunctionField, Divisor.degree D = 0 →
      (Divisor.IsPrincipal D ↔ divisorSum D = 0)

section AbelTheorem

variable [AbelTheorem W]

end AbelTheorem

end WeierstrassCurve.Affine

end
