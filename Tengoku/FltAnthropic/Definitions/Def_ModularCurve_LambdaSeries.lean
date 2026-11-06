import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_KroneckerTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def lambdaInt : LaurentSeries ℤ :=
  HahnSeries.single (1 : ℤ) (1 : ℤ) *
    HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 *
    qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
    qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)

def lambdaModC (L : Type*) [CommRing L] : LaurentSeries L :=
  laurentMap (Int.castRingHom L) lambdaInt

def lambdaNModC (L : Type*) [CommRing L] (N : ℕ) [NeZero N] : LaurentSeries L :=
  qExpand L N (lambdaModC L)

def evalAtLambdaInt : Polynomial ℤ →+* LaurentSeries ℤ :=
  Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) lambdaInt

end ModularCurve

end
