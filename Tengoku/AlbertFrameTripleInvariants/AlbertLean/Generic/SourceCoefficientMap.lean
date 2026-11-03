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

@[simp] theorem mapF0_apply (f : K →+* L) (x : F0Coord K) (i : Fin 27) :
    mapF0 f x i = f (x i) := rfl

theorem mapF0_injective (f : K →+* L) : Function.Injective (mapF0 f) := by
  intro x y h
  funext i
  exact f.injective (congrFun h i)

@[simp] theorem mapF0_zero (f : K →+* L) : mapF0 f 0 = 0 := by ext; simp [mapF0]
@[simp] theorem mapF0_add (f : K →+* L) (x y : F0Coord K) :
    mapF0 f (x + y) = mapF0 f x + mapF0 f y := by ext; simp [mapF0]
@[simp] theorem mapF0_sub (f : K →+* L) (x y : F0Coord K) :
    mapF0 f (x - y) = mapF0 f x - mapF0 f y := by ext; simp [mapF0]
@[simp] theorem mapF0_smul (f : K →+* L) (a : K) (x : F0Coord K) :
    mapF0 f (a • x) = f a • mapF0 f x := by ext; simp [mapF0]

@[simp] theorem mapF0_id (x : F0Coord K) : mapF0 (RingHom.id K) x = x := by ext; rfl

theorem mapF0_comp (g : L →+* M) (f : K →+* L) (x : F0Coord K) :
    mapF0 g (mapF0 f x) = mapF0 (g.comp f) x := by ext; rfl

@[simp] theorem mapF0_one (f : K →+* L) : mapF0 f f0OneK = f0OneK := by
  funext i
  fin_cases i <;> simp [mapF0, f0OneK]

theorem mapF0_trace (f : K →+* L) (x : F0Coord K) :
    f0TraceK (mapF0 f x) = f (f0TraceK x) := by simp [f0TraceK, mapF0]

/-- The sole tensor calculation needed for coefficient naturality.-/
theorem mapF0_product (f : K →+* L) (x y : F0Coord K) :
    mapF0 f (f0ProductK x y) = f0ProductK (mapF0 f x) (mapF0 f y) := by
  funext c
  simp [f0ProductK, tensorCoeffK, mapF0, map_sum, map_mul]

def mapSource (f : K →+* L) (x : JCoord K) : JCoord L :=
  (structuredEquivK L).symm (mapF0 f (structuredEquivK K x))

theorem mapSource_injective (f : K →+* L) : Function.Injective (mapSource f) := by
  intro x y h
  apply (structuredEquivK K).injective
  apply mapF0_injective f
  simpa only [mapSource, LinearEquiv.apply_symm_apply] using congrArg (structuredEquivK L) h

@[simp] theorem mapSource_zero (f : K →+* L) : mapSource f 0 = 0 := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

@[simp] theorem mapSource_add (f : K →+* L) (x y : JCoord K) :
    mapSource f (x + y) = mapSource f x + mapSource f y := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

@[simp] theorem mapSource_sub (f : K →+* L) (x y : JCoord K) :
    mapSource f (x - y) = mapSource f x - mapSource f y := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

@[simp] theorem mapSource_smul (f : K →+* L) (a : K) (x : JCoord K) :
    mapSource f (a • x) = f a • mapSource f x := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

@[simp] theorem mapSource_id (x : JCoord K) : mapSource (RingHom.id K) x = x := by
  apply (structuredEquivK K).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, map_zero, map_add, map_sub,
    map_smul, mapF0_zero, mapF0_add, mapF0_sub, mapF0_smul, mapF0_id]

theorem mapSource_comp (g : L →+* M) (f : K →+* L) (x : JCoord K) :
    mapSource g (mapSource f x) = mapSource (g.comp f) x := by
  apply (structuredEquivK M).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, mapF0_comp]

@[simp] theorem mapSource_one (f : K →+* L) :
    mapSource f sourceOne = sourceOne := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply, structuredEquivK_sourceOne, mapF0_one]

@[simp] theorem mapSource_trace (f : K →+* L) (x : JCoord K) :
    sourceTrace (mapSource f x) = f (sourceTrace x) := by
  rw [sourceTrace_agrees_with_f0K, sourceTrace_agrees_with_f0K]
  simp only [mapSource, LinearEquiv.apply_symm_apply, mapF0_trace]

@[simp] theorem mapSource_product (f : K →+* L) (x y : JCoord K) :
    mapSource f (sourceProduct x y) =
      sourceProduct (mapSource f x) (mapSource f y) := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply,
    GenericStructuredProductAgreesWithF0, mapF0_product]

@[simp] theorem mapSource_diagonalUnit (f : K →+* L) (i : Fin 3) :
    mapSource f (diagonalUnit i) = diagonalUnit i := by
  apply (structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply]
  fin_cases i <;> funext c <;> fin_cases c <;>
    simp [mapSource, structuredEquivK, structuredToF0K, diagonalUnit, diagonal, mapF0]

end AlbertLean.Generic.SourceCoefficientMap
