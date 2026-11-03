import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericReflectionGauge
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParityEvenConjugation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms vector_factor` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms spinorS_factor` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms spinorC_factor` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms theta_eq_two_even` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.ReflectionEvenFactor

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.SourceEvenReflections
open AlbertLean.Triality.SourceEvenAutomorphism
open AlbertLean.Triality.ParityEvenConjugation
open GenericReflectionGauge

variable {K : Type*} [Field K] [CharZero K]

def axisRZ (a : K) : VCoord K := ⟨1, -a, 0⟩
def axis1234 (a : K) : VCoord K :=
  ⟨0, 0, fun | .i12 => 1 | .i34 => -a | _ => 0⟩
def axis1324 : VCoord K :=
  ⟨0, 0, fun | .i13 => 1 | .i24 => 1 | _ => 0⟩
def axis1423 : VCoord K :=
  ⟨0, 0, fun | .i14 => 1 | .i23 => -1 | _ => 0⟩

@[simp] theorem norm_axisRZ (a : K) : nV (axisRZ a) = -a := by
  simp [axisRZ, nV, pf_coordinate]
@[simp] theorem norm_axis1234 (a : K) : nV (axis1234 a) = -a := by
  simp [axis1234, nV, pf_coordinate]
@[simp] theorem norm_axis1324 : nV (axis1324 : VCoord K) = -1 := by
  simp [axis1324, nV, pf_coordinate]
@[simp] theorem norm_axis1423 : nV (axis1423 : VCoord K) = -1 := by
  simp [axis1423, nV, pf_coordinate]

theorem vector_factor (a : K) (ha : a ≠ 0) (v : VCoord K) :
    evenV (axisRZ a) (axis1234 a) (evenV axis1324 axis1423 v) =
      thetaV a v := by
  apply VCoord.ext
  · simp [evenV, reflectV, axisRZ, axis1234, axis1324, axis1423,
      BV, nV, pf_coordinate, BW, thetaV, ha] <;> field_simp [ha] <;> ring
  · simp [evenV, reflectV, axisRZ, axis1234, axis1324, axis1423,
      BV, nV, pf_coordinate, BW, thetaV, ha] <;> field_simp [ha] <;> ring
  · funext i
    cases i <;>
      simp [evenV, reflectV, axisRZ, axis1234, axis1324, axis1423,
        BV, nV, pf_coordinate, BW, thetaV, ha] <;> field_simp [ha] <;> ring

theorem spinorS_factor (a : K) (ha : a ≠ 0) (s : SCoord K) :
    evenS (axisRZ a) (axis1234 a) a (evenS axis1324 axis1423 1 s) =
      thetaS a s := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;>
    simp [evenS, sourceMuS, sourceMuC, axisRZ, axis1234,
      axis1324, axis1423, thetaS, smul_eq_mul, ha] <;> field_simp [ha] <;> ring

theorem spinorC_factor (a : K) (ha : a ≠ 0) (c : CCoord K) :
    evenC (axisRZ a) (axis1234 a) a (evenC axis1324 axis1423 1 c) =
      thetaC a c := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;>
    simp [evenC, sourceMuS, sourceMuC, axisRZ, axis1234,
      axis1324, axis1423, thetaC, smul_eq_mul, ha] <;> field_simp [ha] <;> ring

/-- The orientation correction is two normalized even pairs. The inner
pair is constant over the prime field; neither pair needs a new root.-/
theorem theta_eq_two_even (a : K) (ha : a ≠ 0) (x : JCoord K) :
    (sourceEvenAut (axisRZ a) (axis1234 a) a
      (by simpa using neg_ne_zero.mpr ha)
      (by simpa using neg_ne_zero.mpr ha)
      (by simp [pow_two]) ha).linear
      ((sourceEvenAut (axis1324 : VCoord K) axis1423 1
        (by simp) (by simp) (by simp) (by norm_num)).linear x) =
      theta a x := by
  simp only [sourceEvenAut_linear_apply]
  exact JCoord.ext rfl rfl rfl (vector_factor a ha x.v)
    (spinorS_factor a ha x.s) (spinorC_factor a ha x.c)

end AlbertLean.Generic.ReflectionEvenFactor
