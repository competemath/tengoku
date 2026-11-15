import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_GenusOnePic0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F]

variable (W : Affine F) in

class GenusOnePlaceGate.IsCentred [GenusOnePlaceGate W] : Prop where

  XClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits

  YClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits

namespace GenusOnePlaceGate.IsCentred

variable {W : Affine F} [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

/--
@isnad1 id=mem.1h4v.s10.03dcef71ce40 from=translated src=- shape=dd0a875e vocab=a42aa0be
-/
theorem algebraMap_XClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  XClass_mem_nonunits x y h

/--
@isnad1 id=mem.1h4v.s10.8b172a1b1e98 from=translated src=- shape=00186eb6 vocab=8a1b81bc
-/
theorem algebraMap_YClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  YClass_mem_nonunits x y h

end GenusOnePlaceGate.IsCentred

end WeierstrassCurve.Affine
