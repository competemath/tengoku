import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.GenericF0Recovery
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.StructuredProductF0
import Tengoku.Seed.LinearAlgebra.Basis.Bilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @GenericStructuredProductAgreesWithF0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms GenericStructuredProductAgreesWithF0` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Generic product transport from the accepted rational comparison

This module extends the accepted rational recovery-product comparison to an
arbitrary characteristic-zero field.  It uses coefficientwise scalar
extension, trace-form uniqueness, and full-vector basis extensionality.  It
does not expand the frozen product into output-coordinate shards.
-/

namespace AlbertLean.Comparison.GenericProductTransport

open AlbertLean
open AlbertLean.CubicNorm
open AlbertLean.Generated
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Triality.GenericCoordinates
open AlbertLean.Comparison.StructuredProductF0
open AlbertLean.Comparison.GenericF0
open AlbertLean.Comparison.GenericF0Recovery

variable {K : Type*} [Field K] [CharZero K]

/-- Coefficientwise scalar extension on the frozen 27-coordinate carrier.-/
def mapCoordQK (K : Type*) [Field K] [CharZero K]
    (x : Coord) : F0Coord K := fun i => algebraMap ℚ K (x i)

/--
@isnad1 id=eq.0h3v.s6.376b1b39a1a9 from=translated src=- shape=0e40e54d vocab=3f0d2290
-/
@[simp] theorem mapCoordQK_apply (x : Coord) (i : Fin 27) :
    mapCoordQK K x i = algebraMap ℚ K (x i) := rfl

/--
@isnad1 id=eq.0h1v.s6.450ad7668867 from=translated src=- shape=db9d6ea0 vocab=bc1ba1f4
-/
@[simp] theorem mapCoordQK_zero : mapCoordQK K (0 : Coord) = 0 := by
  funext i
  simp [mapCoordQK]

/--
@isnad1 id=eq.0h3v.s6.7dbab7115bda from=translated src=- shape=236106f5 vocab=a6d984e4
-/
@[simp] theorem mapCoordQK_add (x y : Coord) :
    mapCoordQK K (x + y) = mapCoordQK K x + mapCoordQK K y := by
  funext i
  simp [mapCoordQK]

/--
@isnad1 id=eq.0h3v.s6.b8153c1776ce from=translated src=- shape=236106f5 vocab=1d275788
-/
@[simp] theorem mapCoordQK_sub (x y : Coord) :
    mapCoordQK K (x - y) = mapCoordQK K x - mapCoordQK K y := by
  funext i
  simp [mapCoordQK]

/--
@isnad1 id=eq.0h3v.s7.0e75dd0cdeab from=translated src=- shape=6751280a vocab=ccd8366a
-/
@[simp] theorem mapCoordQK_smul (a : ℚ) (x : Coord) :
    mapCoordQK K (a • x) = algebraMap ℚ K a • mapCoordQK K x := by
  funext i
  simp [mapCoordQK]

/--
@isnad1 id=eq.0h2v.s8.4ad781ffdec2 from=translated src=- shape=894ab845 vocab=fe27bb37
-/
@[simp] theorem mapCoordQK_basis (i : Fin 27) :
    mapCoordQK K (Pi.basisFun ℚ (Fin 27) i) =
      Pi.basisFun K (Fin 27) i := by
  classical
  funext j
  simp [mapCoordQK, Pi.single_apply]

/--
@isnad1 id=eq.0h1v.s4.d884f1d22e39 from=translated src=- shape=444729a6 vocab=b6440423
-/
@[simp] theorem mapCoordQK_one :
    mapCoordQK K AlbertLean.one = f0OneK := by
  funext i
  fin_cases i <;> simp [mapCoordQK, AlbertLean.one, f0OneK, q]

private theorem vK_mapCoordQK (x : Coord) (n : Nat) :
    vK (mapCoordQK K x) n = algebraMap ℚ K (v x n) := by
  unfold vK v
  split <;> simp_all [mapCoordQK]

/--
@isnad1 id=eq.0h2v.s6.4e5dcf14a270 from=translated src=- shape=969d1d5d vocab=bd6b0855
-/
theorem f0NormK_mapCoordQK (x : Coord) :
    f0NormK (mapCoordQK K x) = algebraMap ℚ K (cubicNorm x) := by
  simp only [f0NormK, cubicNorm, qK, vK_mapCoordQK, map_add, map_mul]

/--
@isnad1 id=eq.0h4v.s6.af9ea5b20b4e from=translated src=- shape=37904ea9 vocab=c4596c16
-/
theorem f0PolarK_mapCoordQK (x y z : Coord) :
    f0PolarK (mapCoordQK K x) (mapCoordQK K y) (mapCoordQK K z) =
      algebraMap ℚ K (cubicPolar x y z) := by
  simp only [f0PolarK, cubicPolar, ← mapCoordQK_add,
    f0NormK_mapCoordQK, map_add, map_sub]
  rw [f0NormK_zero,
    AlbertLean.Comparison.StructuredF0.f0_cubicNorm_zero, map_zero]

/--
@isnad1 id=eq.0h2v.s6.97b453b85a43 from=translated src=- shape=969d1d5d vocab=f37509c0
-/
theorem f0TraceK_mapCoordQK (x : Coord) :
    f0TraceK (mapCoordQK K x) = algebraMap ℚ K (traceN x) := by
  rw [traceN_eq_coords]
  simp [f0TraceK, mapCoordQK]

/--
@isnad1 id=eq.0h3v.s6.40da1f0b8844 from=translated src=- shape=e628c1e3 vocab=37632ded
-/
theorem f0TraceFormK_mapCoordQK (x y : Coord) :
    f0TraceFormK (mapCoordQK K x) (mapCoordQK K y) =
      algebraMap ℚ K (traceForm x y) := by
  rw [f0TraceFormK, traceForm, f0SpurBilinearK, spurBilinear,
    ← mapCoordQK_one, f0TraceK_mapCoordQK, f0TraceK_mapCoordQK,
    f0PolarK_mapCoordQK]
  simp

private theorem mappedAdjoint_characterization (x : Coord) (z : F0Coord K) :
    f0TraceFormK (mapCoordQK K (f0RecoveryData.adjoint x)) z =
      f0PolarK (mapCoordQK K x) (mapCoordQK K x) z / 2 := by
  let b := Pi.basisFun K (Fin 27)
  let lhs : F0Coord K →ₗ[K] K :=
    f0TraceFormLinearK (mapCoordQK K (f0RecoveryData.adjoint x))
  let rhs : F0Coord K →ₗ[K] K :=
    (2 : K)⁻¹ • f0PolarLinearK (mapCoordQK K x) (mapCoordQK K x)
  have hmaps : lhs = rhs := by
    apply b.ext
    intro i
    change f0TraceFormK (mapCoordQK K (f0RecoveryData.adjoint x))
        (Pi.basisFun K (Fin 27) i) =
      (2 : K)⁻¹ * f0PolarK (mapCoordQK K x) (mapCoordQK K x)
        (Pi.basisFun K (Fin 27) i)
    rw [← mapCoordQK_basis (K := K) i, f0TraceFormK_mapCoordQK,
      f0PolarK_mapCoordQK]
    have hQ := f0RecoveryData.adjoint_characterization x
      (Pi.basisFun ℚ (Fin 27) i)
    have hK := congrArg (algebraMap ℚ K) hQ
    simpa [f0RecoveryData, div_eq_mul_inv, mul_comm] using hK
  have hz := congrArg (fun f : F0Coord K →ₗ[K] K => f z) hmaps
  simpa [lhs, rhs, div_eq_mul_inv, mul_comm] using hz

/--
@isnad1 id=eq.0h2v.s7.c2ebbb9ad276 from=translated src=- shape=d2a34f24 vocab=a8c56a47
-/
theorem f0AdjointK_mapCoordQK (x : Coord) :
    (f0RecoveryDataK (K := K)).adjoint (mapCoordQK K x) =
      mapCoordQK K (f0RecoveryData.adjoint x) := by
  apply sub_eq_zero.mp
  apply (f0RecoveryDataK (K := K)).traceForm_nondegenerate
  intro z
  change f0TraceFormLinearK
    ((f0RecoveryDataK (K := K)).adjoint (mapCoordQK K x) -
      mapCoordQK K (f0RecoveryData.adjoint x)) z = 0
  simp only [map_sub, LinearMap.sub_apply, f0TraceFormLinearK_apply]
  have hAdj := (f0RecoveryDataK (K := K)).adjoint_characterization
    (mapCoordQK K x) z
  change f0TraceFormK
    ((f0RecoveryDataK (K := K)).adjoint (mapCoordQK K x)) z =
      f0PolarK (mapCoordQK K x) (mapCoordQK K x) z / 2 at hAdj
  rw [hAdj]
  change f0PolarK (mapCoordQK K x) (mapCoordQK K x) z / 2 -
    f0TraceFormK (mapCoordQK K (f0RecoveryData.adjoint x)) z = 0
  rw [mappedAdjoint_characterization]
  ring

/--
@isnad1 id=eq.0h3v.s7.036fc51d30a0 from=translated src=- shape=afe0ac95 vocab=1ad8939e
-/
theorem f0CrossK_mapCoordQK (x y : Coord) :
    (f0RecoveryDataK (K := K)).cross (mapCoordQK K x) (mapCoordQK K y) =
      mapCoordQK K (f0RecoveryData.cross x y) := by
  simp only [RecoveryData.cross]
  rw [← mapCoordQK_add, f0AdjointK_mapCoordQK,
    f0AdjointK_mapCoordQK, f0AdjointK_mapCoordQK,
    mapCoordQK_sub, mapCoordQK_sub]

/--
@isnad1 id=eq.0h3v.s7.c2f051a25b13 from=translated src=- shape=7d74fdcb vocab=2f8e510e
-/
theorem f0SpurBilinearK_mapCoordQK (x y : Coord) :
    (f0RecoveryDataK (K := K)).spurBilinear
        (mapCoordQK K x) (mapCoordQK K y) =
      algebraMap ℚ K (f0RecoveryData.spurBilinear x y) := by
  simp [RecoveryData.spurBilinear, f0RecoveryDataK, f0RecoveryData,
    f0TraceK_mapCoordQK, f0TraceFormK_mapCoordQK]

/--
@isnad1 id=eq.0h3v.s7.b0ae419c1b3e from=translated src=- shape=afe0ac95 vocab=2c1c464f
-/
theorem f0RecoveredProductK_mapCoordQK (x y : Coord) :
    (f0RecoveryDataK (K := K)).product
        (mapCoordQK K x) (mapCoordQK K y) =
      mapCoordQK K (f0RecoveryData.product x y) := by
  simp only [RecoveryData.product]
  rw [f0CrossK_mapCoordQK]
  rw [f0SpurBilinearK_mapCoordQK]
  simp [f0RecoveryDataK, f0RecoveryData, f0TraceK_mapCoordQK,
    mapCoordQK_one, mapCoordQK_add,
    mapCoordQK_sub, mapCoordQK_smul]

/--
@isnad1 id=eq.0h3v.s5.d73c3aad705a from=translated src=- shape=a839dbd8 vocab=68f5ae31
-/
theorem f0ProductK_mapCoordQK (x y : Coord) :
    f0ProductK (mapCoordQK K x) (mapCoordQK K y) =
      mapCoordQK K (structuredProduct x y) := by
  rw [structuredProduct_eq_tensor]
  funext k
  simp [f0ProductK, tensorProduct, tensorCoeffK, mapCoordQK,
    map_sum, map_mul]

/-- The formulaic generic F0 tensor product as a curried linear map.-/
def f0ProductLinearK : F0Coord K →ₗ[K] F0Coord K →ₗ[K] F0Coord K where
  toFun x :=
    { toFun := f0ProductK x
      map_add' := f0ProductK_add_right x
      map_smul' := fun a y => f0ProductK_smul_right a x y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact f0ProductK_add_left x y z
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    exact f0ProductK_smul_left a x y

/--
@isnad1 id=eq.0h3v.s10.f828b4681e94 from=translated src=- shape=229a5892 vocab=a861fb3f
-/
@[simp] theorem f0ProductLinearK_apply (x y : F0Coord K) :
    f0ProductLinearK x y = f0ProductK x y := rfl

private theorem f0RecoveredProductK_basis (i j : Fin 27) :
    (f0RecoveryDataK (K := K)).product
        (Pi.basisFun K (Fin 27) i) (Pi.basisFun K (Fin 27) j) =
      f0ProductK (Pi.basisFun K (Fin 27) i)
        (Pi.basisFun K (Fin 27) j) := by
  calc
    _ = mapCoordQK K
        (f0RecoveryData.product (Pi.basisFun ℚ (Fin 27) i)
          (Pi.basisFun ℚ (Fin 27) j)) := by
          rw [← mapCoordQK_basis (K := K) i,
            ← mapCoordQK_basis (K := K) j]
          exact f0RecoveredProductK_mapCoordQK (K := K)
            (Pi.basisFun ℚ (Fin 27) i) (Pi.basisFun ℚ (Fin 27) j)
    _ = mapCoordQK K
        (structuredProduct (Pi.basisFun ℚ (Fin 27) i)
          (Pi.basisFun ℚ (Fin 27) j)) := by
          exact congrArg (mapCoordQK K)
            (f0RecoveredProduct_eq_structuredProduct _ _)
    _ = f0ProductK (Pi.basisFun K (Fin 27) i)
        (Pi.basisFun K (Fin 27) j) := by
          symm
          rw [← mapCoordQK_basis (K := K) i,
            ← mapCoordQK_basis (K := K) j]
          exact f0ProductK_mapCoordQK (K := K)
            (Pi.basisFun ℚ (Fin 27) i) (Pi.basisFun ℚ (Fin 27) j)

/--
@isnad1 id=eq.0h3v.s6.7896cdb4af86 from=translated src=- shape=62801b42 vocab=746851a5
-/
theorem f0RecoveredProductK_eq_f0ProductK (x y : F0Coord K) :
    (f0RecoveryDataK (K := K)).product x y = f0ProductK x y := by
  have hmaps : f0RecoveredProductLinearK (K := K) =
      f0ProductLinearK (K := K) := by
    apply LinearMap.ext_basis (Pi.basisFun K (Fin 27))
      (Pi.basisFun K (Fin 27))
    intro i j
    simpa using f0RecoveredProductK_basis (K := K) i j
  simpa only [f0RecoveredProductLinearK_apply, f0ProductLinearK_apply] using
    congrArg
      (fun B : F0Coord K →ₗ[K] F0Coord K →ₗ[K] F0Coord K => B x y) hmaps

/-- The generic source product agrees with the independently frozen F0 tensor.
@isnad1 id=eq.0h3v.s10.f56f9bf98718 from=translated src=- shape=1bc831e8 vocab=b8e8e851
-/
theorem GenericStructuredProductAgreesWithF0 {K : Type*}
    [Field K] [CharZero K] :
    ∀ x y : JCoord K,
      structuredEquivK K (sourceProduct x y) =
        f0ProductK (structuredEquivK K x) (structuredEquivK K y) := by
  intro x y
  rw [structuredEquivK_map_sourceProduct_to_genericRecovery,
    f0RecoveredProductK_eq_f0ProductK]

end AlbertLean.Comparison.GenericProductTransport
