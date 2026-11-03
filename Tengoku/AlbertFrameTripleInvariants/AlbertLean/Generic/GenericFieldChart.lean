import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericNormalizedFrameChart
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericDeterminantOpen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms genericOpen` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms genericChart_source_fixedSpectrum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deck_Delta` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deck_involutive` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# The actual nested generic point of the normalized frame chart

The nineteen base coordinates live first in `B = Frac(k[BaseVar])`.  They
are then embedded into `Omega = Frac(B[T])`, with `Delta = T`.  Every field
of `OpenParameters` is discharged from polynomial nonvanishing proved in
`GenericDeterminantOpen` and the degree-two branch lemma proved in
`NestedReciprocalField`.
-/

noncomputable section

namespace AlbertLean.Generic.GenericFieldChart

open Matrix
open AlbertLean.Generic.GenericNormalizedFrameChart
open AlbertLean.Generic.NestedReciprocalField
open AlbertLean.Generic.GenericDeterminantOpen

universe u
variable (k : Type u) [Field k] [CharZero k]

abbrev Base := GenericDeterminantOpen.B k
abbrev FunctionField := Omega (Base k)

/--
@isnad1 id=charzero.0h1v.s7.a9e1223ecc93 from=translated src=- shape=d96e9922 vocab=1dc04ac8
-/
instance baseCharZero : CharZero (Base k) where
  cast_injective n m h := by
    apply (Nat.cast_injective (R := k))
    apply (algebraMap k (Base k)).injective
    simpa only [map_natCast] using h

/--
@isnad1 id=charzero.0h1v.s9.5d822b3565f0 from=translated src=- shape=d96e9922 vocab=13a0ae7c
-/
instance fieldCharZero : CharZero (FunctionField k) where
  cast_injective n m h := by
    apply (Nat.cast_injective (R := Base k))
    apply (algebraMap (Base k) (FunctionField k)).injective
    simpa only [map_natCast] using h

/-- The nineteen base coordinates.  Its `Delta` placeholder is irrelevant
to `moment`; the actual independent root is inserted only after extension to
`FunctionField k`.-/
def baseParameters : Parameters (Base k) where
  dA0 := ι k (GenericDeterminantOpen.dA0 k)
  dA1 := ι k (GenericDeterminantOpen.dA1 k)
  dB0 := ι k (GenericDeterminantOpen.dB0 k)
  dB1 := ι k (GenericDeterminantOpen.dB1 k)
  a := ι k (GenericDeterminantOpen.a k)
  b := ι k (GenericDeterminantOpen.b k)
  c := ι k (GenericDeterminantOpen.c k)
  offDiag := fun ij h => ι k (offX k ⟨ij,h⟩)
  Delta := 1

/--
@isnad1 id=eq.0h1v.s8.6bcd9d02c91c from=translated src=- shape=733fd0d8 vocab=84796307
-/
theorem baseParameters_pivotA : pivotA (baseParameters k) = ι k (PA k) := by
  simp [pivotA, GenericNormalizedFrameChart.dA2, baseParameters, PA,
    GenericDeterminantOpen.dA2]

/--
@isnad1 id=eq.0h1v.s8.7f3e6b951028 from=translated src=- shape=733fd0d8 vocab=8c401972
-/
theorem baseParameters_pivotB : pivotB (baseParameters k) = ι k (PB k) := by
  simp [pivotB, GenericNormalizedFrameChart.dB2, baseParameters, PB,
    GenericDeterminantOpen.dB2]

/-- The solved chart moment is literally the previously proved generic
rational moment.
@isnad1 id=eq.0h1v.s6.62c21d3b57a1 from=translated src=- shape=b205a460 vocab=6ca5b3a4
-/
theorem baseParameters_moment : moment (baseParameters k) = rationalM k := by
  have ha := PA_ne_zero k
  have hb := PB_ne_zero k
  have hea : ι k (PA k) = ι k (diagX k 0) + ι k (diagX k 1) * 2 := by
    simp [PA, GenericDeterminantOpen.dA2, GenericDeterminantOpen.dA0,
      GenericDeterminantOpen.dA1]
    ring
  have heb : ι k (PB k) = ι k (diagX k 2) + ι k (diagX k 3) * 2 := by
    simp [PB, GenericDeterminantOpen.dB2, GenericDeterminantOpen.dB0,
      GenericDeterminantOpen.dB1]
    ring
  rw [hea] at ha
  rw [heb] at hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [moment, rationalM, baseParameters, m00, m11, m22, m33,
      normWeightedA, normWeightedB, spurSumA, spurSumB, pivotA, pivotB,
      GenericNormalizedFrameChart.dA2, GenericNormalizedFrameChart.dB2,
      rawOffDiag, nA0, nA2, nB1, nB3, TA, TB, SA, SB,
      GenericDeterminantOpen.dA2, GenericDeterminantOpen.dB2,
      GenericDeterminantOpen.dA0, GenericDeterminantOpen.dA1,
      GenericDeterminantOpen.dB0, GenericDeterminantOpen.dB1,
      GenericDeterminantOpen.a, GenericDeterminantOpen.b,
      GenericDeterminantOpen.c, off, PA, PB, PA_ne_zero, PB_ne_zero] <;>
    ring_nf <;> field_simp [ha, hb] <;> ring

def includeBase : Base k →+* FunctionField k := algebraMap (Base k) (FunctionField k)

/-- The actual twenty-coordinate point in the nested rational function
field, with all nineteen coefficients constant in `T`.-/
def fieldParameters : Parameters (FunctionField k) where
  dA0 := includeBase k (baseParameters k).dA0
  dA1 := includeBase k (baseParameters k).dA1
  dB0 := includeBase k (baseParameters k).dB0
  dB1 := includeBase k (baseParameters k).dB1
  a := includeBase k (baseParameters k).a
  b := includeBase k (baseParameters k).b
  c := includeBase k (baseParameters k).c
  offDiag := fun ij h => includeBase k ((baseParameters k).offDiag ij h)
  Delta := T (Base k)

/--
@isnad1 id=eq.0h1v.s10.00443a3c0f80 from=translated src=- shape=e3f4b1bd vocab=dde8dc08
-/
theorem fieldParameters_moment : moment (fieldParameters k) =
    (rationalM k).map (includeBase k) := by
  rw [← baseParameters_moment k]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [moment, fieldParameters, baseParameters, m00, m11, m22, m33,
      normWeightedA, normWeightedB, spurSumA, spurSumB, pivotA, pivotB,
      GenericNormalizedFrameChart.dA2, GenericNormalizedFrameChart.dB2,
      rawOffDiag, includeBase, map_div₀]

/--
@isnad1 id=eq.0h1v.s11.c483e25908f7 from=translated src=- shape=878d88f2 vocab=f6d49692
-/
theorem fieldParameters_detMoment :
    Matrix.det (moment (fieldParameters k)) =
      includeBase k (Matrix.det (rationalM k)) := by
  rw [fieldParameters_moment]
  exact (RingHom.map_det (includeBase k) (rationalM k)).symm

def genericOpen : OpenParameters (FunctionField k) where
  toParameters := fieldParameters k
  pivotA_ne := by
    rw [show pivotA (fieldParameters k) =
      includeBase k (pivotA (baseParameters k)) by
        simp [pivotA, GenericNormalizedFrameChart.dA2,
          fieldParameters, includeBase]]
    rw [baseParameters_pivotA]
    exact (map_ne_zero (includeBase k)).mpr (PA_ne_zero k)
  pivotB_ne := by
    rw [show pivotB (fieldParameters k) =
      includeBase k (pivotB (baseParameters k)) by
        simp [pivotB, GenericNormalizedFrameChart.dB2,
          fieldParameters, includeBase]]
    rw [baseParameters_pivotB]
    exact (map_ne_zero (includeBase k)).mpr (PB_ne_zero k)
  Delta_ne := T_ne_zero (Base k)
  detMoment_ne := by
    rw [fieldParameters_detMoment]
    exact (map_ne_zero (includeBase k)).mpr (det_rationalM_ne_zero k)
  branch_ne := by
    rw [fieldParameters_detMoment]
    exact fun h =>
      (branchPolynomial_ne_zero (Base k) (Matrix.det (rationalM k)))
        (sub_eq_zero.mpr h)

def genericChart := insert (genericOpen k)

/--
@isnad1 id=and.0h1v.s13.0198b838b620 from=translated src=- shape=486e23e8 vocab=4103ff30
-/
theorem genericChart_source_fixedSpectrum :
    AlbertLean.Triality.StructuredCubic.sourceTrace
        (AlbertLean.Residual.FrameIdeal.encoderA (genericChart k)) = 0 ∧
      AlbertLean.Triality.StructuredCubic.sourceSpur
        (AlbertLean.Residual.FrameIdeal.encoderA (genericChart k)) = -1 ∧
      AlbertLean.Triality.StructuredCubic.sourceNorm
        (AlbertLean.Residual.FrameIdeal.encoderA (genericChart k)) = 0 ∧
      AlbertLean.Triality.StructuredCubic.sourceTrace
        (AlbertLean.Residual.FrameIdeal.encoderB (genericChart k)) = 0 ∧
      AlbertLean.Triality.StructuredCubic.sourceSpur
        (AlbertLean.Residual.FrameIdeal.encoderB (genericChart k)) = -1 ∧
      AlbertLean.Triality.StructuredCubic.sourceNorm
        (AlbertLean.Residual.FrameIdeal.encoderB (genericChart k)) = 0 := by
  exact insert_source_fixedSpectrum (genericOpen k)

def deck : FunctionField k ≃+* FunctionField k :=
  reciprocalEquiv (Base k) (Matrix.det (rationalM k))
    (det_rationalM_ne_zero k)

/--
@isnad1 id=eq.0h1v.s13.35d1ebeaae9b from=translated src=- shape=3a883d52 vocab=2686a780
-/
@[simp] theorem deck_Delta : deck k (fieldParameters k).Delta =
    includeBase k (Matrix.det (rationalM k)) / (fieldParameters k).Delta := by
  exact reciprocalEquiv_T (Base k) _ _

/--
@isnad1 id=eq.0h2v.s13.0a2073ae0378 from=translated src=- shape=29c6af02 vocab=74f87a2d
-/
@[simp] theorem deck_base (b : Base k) :
    deck k (includeBase k b) = includeBase k b := by
  exact reciprocalHom_base (Base k) (Matrix.det (rationalM k))
    (det_rationalM_ne_zero k) b

/--
@isnad1 id=eq.0h1v.s13.52f5f72ce28f from=translated src=- shape=d5a6b725 vocab=b86481eb
-/
@[simp] theorem deck_involutive : (deck k).trans (deck k) = RingEquiv.refl _ := by
  ext z
  exact (deck k).left_inv z

end AlbertLean.Generic.GenericFieldChart
