import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.GenericCoordinates
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.StructuredF0
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TensorConformance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms f0ProductK` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0ProductK_rat_eq_structuredProduct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceNorm_agrees_with_f0K` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms GenericF0CubicComparison` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Formulaic F0 base change and generic cubic comparison

The multiplication below is defined solely by applying `algebraMap ℚ K` to
the frozen rational structure coefficients and evaluating the resulting
finite tensor.  In particular it is not transported from `sourceProduct`.
The adapted source flattening was defined in the source-only
`GenericCoordinates` module before this tensor was opened.
-/

namespace AlbertLean.Comparison.GenericF0

open AlbertLean
open AlbertLean.Generated
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.GenericCoordinates
open AlbertLean.Comparison.StructuredF0

variable {K : Type*} [Field K] [CharZero K]

/-- Map one locked rational scalar into the generic field.-/
def qK (num : Int) (den : Nat) : K := algebraMap ℚ K (q num den)

/-- Safe coordinate lookup for the generic 27-coordinate carrier.-/
def vK (x : F0Coord K) (i : Nat) : K := if h : i < 27 then x ⟨i, h⟩ else 0

/-- The coordinate unit, defined literally rather than by source transport.-/
def f0OneK : F0Coord K := fun i ↦
  match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | _ => 0

/-- The frozen rational product tensor after scalar extension to `K`.-/
def tensorCoeffK (i j k : Fin 27) : K := algebraMap ℚ K (tensorCoeff i j k)

/-- Formulaic scalar extension of the frozen F0 product tensor.-/
def f0ProductK (x y : F0Coord K) : F0Coord K := fun k ↦
  ∑ i : Fin 27, ∑ j : Fin 27, x i * y j * tensorCoeffK i j k

/-- The independently frozen cubic coordinate polynomial over `K`.-/
def f0NormK (x : F0Coord K) : K :=
    qK 1 1 * vK x 0 * vK x 1 * vK x 2 +
    qK (-1) 1 * vK x 0 * vK x 3 * vK x 4 +
    qK (-1) 1 * vK x 0 * vK x 5 * vK x 10 +
    qK 1 1 * vK x 0 * vK x 6 * vK x 9 +
    qK (-1) 1 * vK x 0 * vK x 7 * vK x 8 +
    qK (-1) 1 * vK x 1 * vK x 11 * vK x 15 +
    qK (-1) 1 * vK x 1 * vK x 12 * vK x 16 +
    qK (-1) 1 * vK x 1 * vK x 13 * vK x 17 +
    qK (-1) 1 * vK x 1 * vK x 14 * vK x 18 +
    qK (-1) 1 * vK x 2 * vK x 19 * vK x 23 +
    qK (-1) 1 * vK x 2 * vK x 20 * vK x 24 +
    qK (-1) 1 * vK x 2 * vK x 21 * vK x 25 +
    qK (-1) 1 * vK x 2 * vK x 22 * vK x 26 +
    qK 1 1 * vK x 3 * vK x 15 * vK x 19 +
    qK 1 1 * vK x 3 * vK x 16 * vK x 20 +
    qK 1 1 * vK x 3 * vK x 17 * vK x 21 +
    qK 1 1 * vK x 3 * vK x 18 * vK x 22 +
    qK 1 1 * vK x 4 * vK x 11 * vK x 23 +
    qK 1 1 * vK x 4 * vK x 12 * vK x 24 +
    qK 1 1 * vK x 4 * vK x 13 * vK x 25 +
    qK 1 1 * vK x 4 * vK x 14 * vK x 26 +
    qK 1 1 * vK x 5 * vK x 13 * vK x 22 +
    qK (-1) 1 * vK x 5 * vK x 14 * vK x 21 +
    qK 1 1 * vK x 5 * vK x 15 * vK x 24 +
    qK (-1) 1 * vK x 5 * vK x 16 * vK x 23 +
    qK (-1) 1 * vK x 6 * vK x 12 * vK x 22 +
    qK 1 1 * vK x 6 * vK x 14 * vK x 20 +
    qK 1 1 * vK x 6 * vK x 15 * vK x 25 +
    qK (-1) 1 * vK x 6 * vK x 17 * vK x 23 +
    qK 1 1 * vK x 7 * vK x 12 * vK x 21 +
    qK (-1) 1 * vK x 7 * vK x 13 * vK x 20 +
    qK 1 1 * vK x 7 * vK x 15 * vK x 26 +
    qK (-1) 1 * vK x 7 * vK x 18 * vK x 23 +
    qK 1 1 * vK x 8 * vK x 11 * vK x 22 +
    qK (-1) 1 * vK x 8 * vK x 14 * vK x 19 +
    qK 1 1 * vK x 8 * vK x 16 * vK x 25 +
    qK (-1) 1 * vK x 8 * vK x 17 * vK x 24 +
    qK (-1) 1 * vK x 9 * vK x 11 * vK x 21 +
    qK 1 1 * vK x 9 * vK x 13 * vK x 19 +
    qK 1 1 * vK x 9 * vK x 16 * vK x 26 +
    qK (-1) 1 * vK x 9 * vK x 18 * vK x 24 +
    qK 1 1 * vK x 10 * vK x 11 * vK x 20 +
    qK (-1) 1 * vK x 10 * vK x 12 * vK x 19 +
    qK 1 1 * vK x 10 * vK x 17 * vK x 26 +
    qK (-1) 1 * vK x 10 * vK x 18 * vK x 25

/-- Complete finite-difference polarization of the generic cubic.-/
def f0PolarK (x y z : F0Coord K) : K :=
  f0NormK (x + y + z) - f0NormK (x + y) - f0NormK (x + z) -
  f0NormK (y + z) + f0NormK x + f0NormK y + f0NormK z - f0NormK 0

/-- The literal coordinate trace.-/
def f0TraceK (x : F0Coord K) : K := x 0 + x 1 + x 2

def f0SpurBilinearK (x y : F0Coord K) : K := f0PolarK f0OneK x y
def f0SpurK (x : F0Coord K) : K := f0SpurBilinearK x x / 2
def f0TraceFormK (x y : F0Coord K) : K :=
  f0TraceK x * f0TraceK y - f0SpurBilinearK x y

theorem f0ProductK_add_left (x₁ x₂ y : F0Coord K) :
    f0ProductK (x₁ + x₂) y = f0ProductK x₁ y + f0ProductK x₂ y := by
  funext k
  simp [f0ProductK, Finset.sum_add_distrib, add_mul]

theorem f0ProductK_smul_left (a : K) (x y : F0Coord K) :
    f0ProductK (a • x) y = a • f0ProductK x y := by
  funext k
  simp [f0ProductK, Finset.mul_sum]
  ring

theorem f0ProductK_add_right (x y₁ y₂ : F0Coord K) :
    f0ProductK x (y₁ + y₂) = f0ProductK x y₁ + f0ProductK x y₂ := by
  funext k
  simp only [f0ProductK, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem f0ProductK_smul_right (a : K) (x y : F0Coord K) :
    f0ProductK x (a • y) = a • f0ProductK x y := by
  funext k
  simp only [f0ProductK, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- At `K = ℚ`, the generic coefficient is definitionally the frozen one.-/
theorem tensorCoeffK_rat (i j k : Fin 27) :
    tensorCoeffK (K := ℚ) i j k = tensorCoeff i j k := by
  simp [tensorCoeffK]

/-- At `K = ℚ`, the formulaic generic product is the generated tensor product.-/
theorem f0ProductK_rat (x y : F0Coord ℚ) :
    f0ProductK x y = tensorProduct x y := by
  funext k
  simp [f0ProductK, tensorProduct, tensorCoeffK]

/-- At `K = ℚ`, the generic product specializes to frozen `structuredProduct`.-/
theorem f0ProductK_rat_eq_structuredProduct (x y : F0Coord ℚ) :
    f0ProductK x y = structuredProduct x y := by
  rw [f0ProductK_rat, ← structuredProduct_eq_tensor]

/-- The generic flattening specializes exactly to the accepted rational one.-/
theorem structuredEquivK_rat (x : JCoord ℚ) :
    structuredEquivK ℚ x = structuredEquiv x := rfl

@[simp] theorem structuredEquivK_sourceOne :
    structuredEquivK K (sourceOne : JCoord K) = f0OneK := by
  funext i
  fin_cases i <;> simp [structuredEquivK, structuredToF0K, sourceOne, f0OneK]

theorem f0NormK_zero : f0NormK (0 : F0Coord K) = 0 := by
  simp [f0NormK, vK]

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 100000 in
/-- Universal generic equality of the source cubic and independent coordinate polynomial.-/
theorem sourceNorm_agrees_with_f0K (x : JCoord K) :
    sourceNorm x = f0NormK (structuredEquivK K x) := by
  simp [sourceNorm, f0NormK, structuredEquivK, structuredToF0K, vK, qK, q,
    nV, nS, nC, triality, Pf, BW, evalU, pairW, wedge2, dualWedge2]
  ring

theorem sourceTrace_agrees_with_f0K (x : JCoord K) :
    sourceTrace x = f0TraceK (structuredEquivK K x) := rfl

theorem sourcePolar_agrees_with_f0K (x y z : JCoord K) :
    sourcePolar x y z =
      f0PolarK (structuredEquivK K x) (structuredEquivK K y)
        (structuredEquivK K z) := by
  simp only [sourcePolar, f0PolarK, sourceNorm_agrees_with_f0K, map_add,
    f0NormK_zero]
  ring

theorem sourceSpurBilinear_agrees_with_f0K (x y : JCoord K) :
    sourceSpurPolar x y =
      f0SpurBilinearK (structuredEquivK K x) (structuredEquivK K y) := by
  rw [← sourcePolar_one, sourcePolar_agrees_with_f0K,
    structuredEquivK_sourceOne]
  rfl

theorem sourceSpur_agrees_with_f0K (x : JCoord K) :
    sourceSpur x = f0SpurK (structuredEquivK K x) := by
  rw [f0SpurK, ← sourceSpurBilinear_agrees_with_f0K,
    sourceSpurPolar_diagonal]
  ring

theorem sourceTraceForm_agrees_with_f0K (x y : JCoord K) :
    sourceTraceForm x y =
      f0TraceFormK (structuredEquivK K x) (structuredEquivK K y) := by
  rw [sourceTraceForm, f0TraceFormK, ← sourceTrace_agrees_with_f0K,
    ← sourceTrace_agrees_with_f0K, ← sourceSpurBilinear_agrees_with_f0K]

/-- Literal base change plus generic `T/S/N/P/B` agreement.-/
theorem GenericF0CubicComparison :
    (structuredEquivK K (sourceOne : JCoord K) = f0OneK) ∧
    (∀ x : JCoord K,
      sourceTrace x = f0TraceK (structuredEquivK K x) ∧
      sourceSpur x = f0SpurK (structuredEquivK K x) ∧
      sourceNorm x = f0NormK (structuredEquivK K x)) ∧
    (∀ x y z : JCoord K,
      sourcePolar x y z =
        f0PolarK (structuredEquivK K x) (structuredEquivK K y)
          (structuredEquivK K z)) ∧
    (∀ x y : JCoord K,
      sourceTraceForm x y =
        f0TraceFormK (structuredEquivK K x) (structuredEquivK K y)) := by
  exact ⟨structuredEquivK_sourceOne,
    fun x ↦ ⟨sourceTrace_agrees_with_f0K x, sourceSpur_agrees_with_f0K x,
      sourceNorm_agrees_with_f0K x⟩,
    sourcePolar_agrees_with_f0K, sourceTraceForm_agrees_with_f0K⟩

end AlbertLean.Comparison.GenericF0
