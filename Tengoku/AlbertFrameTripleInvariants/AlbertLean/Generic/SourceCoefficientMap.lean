import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.GenericProductTransport
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualLedgerPower
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms mapF0_product` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapSource_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapSource_comp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapSource_smul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapSource_product` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapSource_trace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapSource_diagonalUnit` (it only prints; the queue checks the axioms of every declaration). -/

/-! Coefficient change for the actual source algebra, factored through the
accepted frozen F0 coordinates.  This is a map of carriers/products, not an
extension operation on arbitrary source automorphisms. -/

noncomputable section
namespace AlbertLean.Generic.SourceCoefficientMap

open scoped BigOperators
open AlbertLean Triality CoordinateTensor StructuredCubic StructuredProduct
open Triality.GenericCoordinates
open Comparison.GenericF0 Comparison.GenericProductTransport
open ResidualLedgerPower

universe u v w
variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [CharZero K] [Field L] [CharZero L]
variable [Field M] [CharZero M]

def mapF0 (f : K →+* L) (x : F0Coord K) : F0Coord L := fun i => f (x i)

/--
@isnad1 id=eq.0h5v.s6.7e530985cc29 from=translated src=- shape=e9dcacb5 vocab=e3877746
-/
@[simp] theorem mapF0_apply (f : K →+* L) (x : F0Coord K) (i : Fin 27) :
    mapF0 f x i = f (x i) := rfl

/--
@isnad1 id=injectiv.0h3v.s6.0d0cf1172da5 from=translated src=- shape=8f34adaf vocab=f4cac014
-/
theorem mapF0_injective (f : K →+* L) : Function.Injective (mapF0 f) := by
  intro x y h
  funext i
  exact f.injective (congrFun h i)

/--
@isnad1 id=eq.0h3v.s7.477d1fab33fa from=translated src=- shape=d3c7f18e vocab=cd6c9069
-/
@[simp] theorem mapF0_zero (f : K →+* L) : mapF0 f 0 = 0 := by ext; simp [mapF0]
/--
@isnad1 id=eq.0h5v.s7.b6dc36e6b4a9 from=translated src=- shape=c1c9629d vocab=8510f923
-/
@[simp] theorem mapF0_add (f : K →+* L) (x y : F0Coord K) :
    mapF0 f (x + y) = mapF0 f x + mapF0 f y := by ext; simp [mapF0]
/--
@isnad1 id=eq.0h5v.s7.b9b01d995386 from=translated src=- shape=c1c9629d vocab=2ee76951
-/
@[simp] theorem mapF0_sub (f : K →+* L) (x y : F0Coord K) :
    mapF0 f (x - y) = mapF0 f x - mapF0 f y := by ext; simp [mapF0]
/--
@isnad1 id=eq.0h5v.s7.8751eb5bbbd0 from=translated src=- shape=d5598f76 vocab=b2f22d14
-/
@[simp] theorem mapF0_smul (f : K →+* L) (a : K) (x : F0Coord K) :
    mapF0 f (a • x) = f a • mapF0 f x := by ext; simp [mapF0]

/--
@isnad1 id=eq.0h2v.s5.c0ecfd3852a3 from=translated src=- shape=000b2749 vocab=ee0469f0
-/
@[simp] theorem mapF0_id (x : F0Coord K) : mapF0 (RingHom.id K) x = x := by ext; rfl

/--
@isnad1 id=eq.0h6v.s7.03bb9ba7f7d3 from=translated src=- shape=0817b10e vocab=f6467ea0
-/
theorem mapF0_comp (g : L →+* M) (f : K →+* L) (x : F0Coord K) :
    mapF0 g (mapF0 f x) = mapF0 (g.comp f) x := by ext; rfl

/--
@isnad1 id=eq.0h3v.s6.65941b94a891 from=translated src=- shape=1ad2bb96 vocab=44fe97db
-/
@[simp] theorem mapF0_one (f : K →+* L) : mapF0 f f0OneK = f0OneK := by
  funext i
  fin_cases i <;> simp [mapF0, f0OneK]

/--
@isnad1 id=eq.0h4v.s6.cee34074f484 from=translated src=- shape=8b42bc84 vocab=196e4d1e
-/
theorem mapF0_trace (f : K →+* L) (x : F0Coord K) :
    f0TraceK (mapF0 f x) = f (f0TraceK x) := by simp [f0TraceK, mapF0]

/-- The sole tensor calculation needed for coefficient naturality.
@isnad1 id=eq.0h5v.s6.a1fda4cc27bb from=translated src=- shape=47357877 vocab=bc4e59f6
-/
theorem mapF0_product (f : K →+* L) (x y : F0Coord K) :
    mapF0 f (f0ProductK x y) = f0ProductK (mapF0 f x) (mapF0 f y) := by
  funext c
  simp [f0ProductK, tensorCoeffK, mapF0, map_sum, map_mul]

def mapSource (f : K →+* L) (x : JCoord K) : JCoord L :=
  (structuredEquivK L).symm (mapF0 f (structuredEquivK K x))

/--
@isnad1 id=injectiv.0h3v.s6.dcdb32592135 from=translated src=- shape=8f34adaf vocab=eee03365
-/
theorem mapSource_injective (f : K →+* L) : Function.Injective (mapSource f) := by
  intro x y h
  apply (structuredEquivK K).injective
  apply mapF0_injective f
  simpa only [mapSource, LinearEquiv.apply_symm_apply] using congrArg (structuredEquivK L) h

/--
@isnad1 id=eq.0h3v.s7.8dae07845987 from=translated src=- shape=d3c7f18e vocab=9d93cff0
-/
@[simp] theorem mapSource_zero (f : K →+* L) : mapSource f 0 = 0 := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

/--
@isnad1 id=eq.0h5v.s7.95fb7c1071c6 from=translated src=- shape=c1c9629d vocab=9778a540
-/
@[simp] theorem mapSource_add (f : K →+* L) (x y : JCoord K) :
    mapSource f (x + y) = mapSource f x + mapSource f y := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

/--
@isnad1 id=eq.0h5v.s7.ec23a948ec5b from=translated src=- shape=c1c9629d vocab=63549c7a
-/
@[simp] theorem mapSource_sub (f : K →+* L) (x y : JCoord K) :
    mapSource f (x - y) = mapSource f x - mapSource f y := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

/--
@isnad1 id=eq.0h5v.s8.018d9920ecdd from=translated src=- shape=d5598f76 vocab=971f64ec
-/
@[simp] theorem mapSource_smul (f : K →+* L) (a : K) (x : JCoord K) :
    mapSource f (a • x) = f a • mapSource f x := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

/--
@isnad1 id=eq.0h2v.s5.7683d8ca2a71 from=translated src=- shape=000b2749 vocab=75156ed5
-/
@[simp] theorem mapSource_id (x : JCoord K) : mapSource (RingHom.id K) x = x := by
  apply (structuredEquivK K).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

/--
@isnad1 id=eq.0h6v.s7.af8fe6713891 from=translated src=- shape=0817b10e vocab=92c09188
-/
theorem mapSource_comp (g : L →+* M) (f : K →+* L) (x : JCoord K) :
    mapSource g (mapSource f x) = mapSource (g.comp f) x := by
  apply (structuredEquivK M).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, mapF0_comp]

/--
@isnad1 id=eq.0h3v.s6.6b3f60f4f9b8 from=translated src=- shape=1ad2bb96 vocab=5779f4a1
-/
@[simp] theorem mapSource_one (f : K →+* L) :
    mapSource f sourceOne = sourceOne := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, structuredEquivK_sourceOne, mapF0_one]

/--
@isnad1 id=eq.0h4v.s6.ea42737f39a5 from=translated src=- shape=8b42bc84 vocab=0f1f6a9c
-/
@[simp] theorem mapSource_trace (f : K →+* L) (x : JCoord K) :
    sourceTrace (mapSource f x) = f (sourceTrace x) := by
  rw [sourceTrace_agrees_with_f0K, sourceTrace_agrees_with_f0K]
  simp only [mapSource, LinearEquiv.apply_symm_apply, mapF0_trace]

/--
@isnad1 id=eq.0h5v.s6.8271ce9fd494 from=translated src=- shape=47357877 vocab=8500b56d
-/
@[simp] theorem mapSource_product (f : K →+* L) (x y : JCoord K) :
    mapSource f (sourceProduct x y) =
      sourceProduct (mapSource f x) (mapSource f y) := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply,
    GenericStructuredProductAgreesWithF0, mapF0_product]

/--
@isnad1 id=eq.0h4v.s6.6f9a63ec0058 from=translated src=- shape=a1f060d2 vocab=67cd9d7a
-/
@[simp] theorem mapSource_diagonalUnit (f : K →+* L) (i : Fin 3) :
    mapSource f (diagonalUnit i) = diagonalUnit i := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply]
  fin_cases i <;> funext c <;> fin_cases c <;>
    simp [mapSource, structuredEquivK, structuredToF0K, diagonalUnit, diagonal, mapF0]

end AlbertLean.Generic.SourceCoefficientMap
