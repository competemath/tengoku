import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.JordanPolarization
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalSourceJordan
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.GenericProductTransport
import Tengoku.Seed.LinearAlgebra.Multilinear.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms rational_f0_residual_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0Polarization_mapCoordQK` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0Polarization_basis_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0PolarizationMap_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0JordanIdentity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceJordanIdentity` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Generic Jordan extension: grounded reduction

The accepted rational identity extends by coefficient naturality and
four-linear basis extensionality, without coordinate case enumeration.
-/

noncomputable section
namespace AlbertLean.Comparison.GenericJordanExtension

open AlbertLean
open AlbertLean.Triality
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.GenericCoordinates
open AlbertLean.Generic.JordanPolarization
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Comparison.GenericF0
open AlbertLean.Comparison.GenericProductTransport

variable {K : Type*} [Field K] [CharZero K]

private theorem mapCoordQK_self (x : Coord) : mapCoordQK ℚ x = x := by
  funext i
  simp [mapCoordQK]

private theorem f0Product_rat_eq_structuredProduct (x y : Coord) :
    f0ProductK x y = structuredProduct x y := by
  have h := f0ProductK_mapCoordQK (K := ℚ) x y
  rw [mapCoordQK_self x, mapCoordQK_self y,
    mapCoordQK_self (structuredProduct x y)] at h
  exact h

theorem rational_f0_residual_zero (x y : Coord) :
    residual (f0ProductLinearK (K := ℚ)) x y = 0 := by
  rw [residual]
  simp only [f0ProductLinearK_apply, f0Product_rat_eq_structuredProduct]
  exact sub_eq_zero.mpr (AlbertLean.jordanIdentity x y)

theorem rational_f0_polarization_zero (a b c y : Coord) :
    polarization (f0ProductLinearK (K := ℚ)) a b c y = 0 := by
  exact polarization_eq_zero_of_residual_eq_zero
    (f0ProductLinearK (K := ℚ)) rational_f0_residual_zero a b c y

/-- Scalar extension commutes with the explicit six-term polarization.-/
theorem f0Polarization_mapCoordQK (a b c y : Coord) :
    polarization (f0ProductLinearK (K := K))
        (mapCoordQK K a) (mapCoordQK K b)
        (mapCoordQK K c) (mapCoordQK K y) =
      mapCoordQK K
        (polarization (f0ProductLinearK (K := ℚ)) a b c y) := by
  simp only [polarization, term, f0ProductLinearK_apply,
    f0ProductK_mapCoordQK, mapCoordQK_add, mapCoordQK_sub,
    f0Product_rat_eq_structuredProduct]

theorem f0Polarization_basis_zero (i₀ i₁ i₂ i₃ : Fin 27) :
    polarization (f0ProductLinearK (K := K))
        (Pi.basisFun K (Fin 27) i₀) (Pi.basisFun K (Fin 27) i₁)
        (Pi.basisFun K (Fin 27) i₂) (Pi.basisFun K (Fin 27) i₃) = 0 := by
  rw [← mapCoordQK_basis (K := K) i₀,
    ← mapCoordQK_basis (K := K) i₁,
    ← mapCoordQK_basis (K := K) i₂,
    ← mapCoordQK_basis (K := K) i₃,
    f0Polarization_mapCoordQK, rational_f0_polarization_zero,
    mapCoordQK_zero]

/-- Four symbolic basis slots suffice because the polarization is genuinely
four-linear.-/
theorem f0PolarizationMap_eq_zero :
    polarizationMap (f0ProductLinearK (K := K)) = 0 := by
  apply Module.Basis.ext_multilinear
    (fun _ : Fin 4 => Pi.basisFun K (Fin 27))
  intro v
  simp only [polarizationMap_apply, zero_apply]
  exact f0Polarization_basis_zero (K := K) (v 0) (v 1) (v 2) (v 3)

/-- The generic F0 tensor satisfies the Jordan identity.-/
theorem f0JordanIdentity (x y : F0Coord K) :
    f0ProductK (f0ProductK x y) (f0ProductK x x) =
      f0ProductK x (f0ProductK y (f0ProductK x x)) := by
  have hp := congrArg
    (fun F : MultilinearMap K (fun _ : Fin 4 => F0Coord K) (F0Coord K) =>
      F ![x, x, x, y]) (f0PolarizationMap_eq_zero (K := K))
  simp only [polarizationMap_apply, zero_apply] at hp
  change polarization (f0ProductLinearK (K := K)) x x x y = 0 at hp
  rw [polarization_diagonal] at hp
  have hr : residual (f0ProductLinearK (K := K)) x y = 0 :=
    (smul_eq_zero.mp hp).resolve_left (by norm_num)
  exact sub_eq_zero.mp (by
    simpa only [residual, f0ProductLinearK_apply] using hr)

/-- The accepted source product satisfies the Jordan identity over every
characteristic-zero field.-/
theorem sourceJordanIdentity (x y : JCoord K) :
    sourceProduct (sourceProduct x y) (sourceProduct x x) =
      sourceProduct x (sourceProduct y (sourceProduct x x)) := by
  apply (structuredEquivK K).injective
  calc
    structuredEquivK K
        (sourceProduct (sourceProduct x y) (sourceProduct x x)) =
        f0ProductK (structuredEquivK K (sourceProduct x y))
          (structuredEquivK K (sourceProduct x x)) :=
      GenericStructuredProductAgreesWithF0 _ _
    _ = f0ProductK
          (f0ProductK (structuredEquivK K x) (structuredEquivK K y))
          (f0ProductK (structuredEquivK K x) (structuredEquivK K x)) := by
      rw [GenericStructuredProductAgreesWithF0,
        GenericStructuredProductAgreesWithF0]
    _ = f0ProductK (structuredEquivK K x)
          (f0ProductK (structuredEquivK K y)
            (f0ProductK (structuredEquivK K x) (structuredEquivK K x))) :=
      f0JordanIdentity _ _
    _ = f0ProductK (structuredEquivK K x)
          (structuredEquivK K (sourceProduct y (sourceProduct x x))) := by
      rw [GenericStructuredProductAgreesWithF0,
        GenericStructuredProductAgreesWithF0]
    _ = structuredEquivK K
          (sourceProduct x (sourceProduct y (sourceProduct x x))) :=
      (GenericStructuredProductAgreesWithF0 _ _).symm

end AlbertLean.Comparison.GenericJordanExtension
