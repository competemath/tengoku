import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

section LaurentMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

def laurentMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one (R := R) (S := S) f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (R := R) (S := S) f.toNonUnitalRingHom
  map_zero' := by
    ext k
    show f ((0 : LaurentSeries R).coeff k) = (0 : LaurentSeries S).coeff k
    rw [HahnSeries.coeff_zero, HahnSeries.coeff_zero, map_zero]
  map_add' x y := by
    ext k
    show f ((x + y).coeff k) = (x.map f + y.map f).coeff k
    rw [HahnSeries.coeff_add, HahnSeries.coeff_add, map_add]
    rfl

end LaurentMap

section IntegralJ

end IntegralJ

section ReduceModBivar

def reduceModBivar (ℓ : ℕ) :
    Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial (ZMod ℓ)) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ)))

end ReduceModBivar

def KroneckerCongruence (ℓ : ℕ) [NeZero ℓ] (data : ModularPolynomialData ℓ) : Prop :=
  reduceModBivar ℓ data.Φ =
    (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
      (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ)

section IntegralEquation

end IntegralEquation

section ModEquation

variable (ℓ : ℕ)

end ModEquation

section ModFunctionField

variable (ℓ : ℕ) [Fact ℓ.Prime]

end ModFunctionField

end ModularCurve
