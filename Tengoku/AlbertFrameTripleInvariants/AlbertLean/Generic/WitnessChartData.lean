import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.LawfulChart
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessFrames
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessDetector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Structural chart readers for the accepted witness data

The encoder identities are checked in the source record: three diagonal
scalars, the eight vector coordinates, and unchanged spinor fields. The
already proved inverse coordinate map then supplies the public equality.
No product, matrix determinant, or detector is evaluated in this module.
-/

noncomputable section

namespace AlbertLean.Generic.WitnessChart

open AlbertLean
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Generic.ResidualAction
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.CoordinateTensor

/-- The accepted nontrivial determinant root.-/
def witnessScale : ℚ := 410231 / 5832

/-- The first accepted witness, read as an explicit source chart.-/
def witnessChart1 : ExplicitFrameChart ℚ where
  diagA := ![-1 / 3, -1, 4 / 3]
  diagB := ![-1 / 3, -1, 4 / 3]
  r1 := 1
  z1 := 0
  r2 := 0
  z2 := 1
  kappa := 1
  s1 := (f0ToStructured theta1F).s
  s2 := (f0ToStructured theta1K).s
  c1 := (f0ToStructured theta1F).c
  c2 := (f0ToStructured theta1K).c

/-- The second accepted witness, with the identical non-residual chart fields.-/
def witnessChartM : ExplicitFrameChart ℚ :=
  { witnessChart1 with
    s1 := (f0ToStructured thetaMF).s
    s2 := (f0ToStructured thetaMK).s
    c1 := (f0ToStructured thetaMF).c
    c2 := (f0ToStructured thetaMK).c }

private theorem witnessChart1_encoderA :
    encoderA witnessChart1 = f0ToStructured theta1F := by
  apply JCoord.ext
  · change (-1 : ℚ) / 3 = q (-1) 3
    norm_num [q]
  · change (-1 : ℚ) = q (-1) 1
    norm_num [q]
  · change (4 : ℚ) / 3 = q 4 3
    norm_num [q]
  · apply VCoord.ext
    · change (1 : ℚ) = q 1 1
      norm_num [q]
    · rfl
    · funext i
      fin_cases i <;> rfl
  · rfl
  · rfl

private theorem witnessChart1_encoderB :
    encoderB witnessChart1 = f0ToStructured theta1K := by
  apply JCoord.ext
  · change (-1 : ℚ) / 3 = q (-1) 3
    norm_num [q]
  · change (-1 : ℚ) = q (-1) 1
    norm_num [q]
  · change (4 : ℚ) / 3 = q 4 3
    norm_num [q]
  · apply VCoord.ext
    · rfl
    · change (1 : ℚ) = q 1 1
      norm_num [q]
    · funext i
      fin_cases i <;> rfl
  · rfl
  · rfl

private theorem witnessChartM_encoderA :
    encoderA witnessChartM = f0ToStructured thetaMF := by
  apply JCoord.ext
  · change (-1 : ℚ) / 3 = q (-1) 3
    norm_num [q]
  · change (-1 : ℚ) = q (-1) 1
    norm_num [q]
  · change (4 : ℚ) / 3 = q 4 3
    norm_num [q]
  · apply VCoord.ext
    · change (1 : ℚ) = q 1 1
      norm_num [q]
    · rfl
    · funext i
      fin_cases i <;> rfl
  · rfl
  · rfl

private theorem witnessChartM_encoderB :
    encoderB witnessChartM = f0ToStructured thetaMK := by
  apply JCoord.ext
  · change (-1 : ℚ) / 3 = q (-1) 3
    norm_num [q]
  · change (-1 : ℚ) = q (-1) 1
    norm_num [q]
  · change (4 : ℚ) / 3 = q 4 3
    norm_num [q]
  · apply VCoord.ext
    · rfl
    · change (1 : ℚ) = q 1 1
      norm_num [q]
    · funext i
      fin_cases i <;> rfl
  · rfl
  · rfl

/--
@isnad1 id=eq.0h0v.s2.5c638f27515e from=translated src=- shape=4b736592 vocab=4f2cc91b
-/
theorem witnessChart1_f0EncoderA : f0EncoderA witnessChart1 = theta1F := by
  change structuredToF0 (encoderA witnessChart1) = theta1F
  rw [witnessChart1_encoderA, structuredToF0_f0ToStructured]

/--
@isnad1 id=eq.0h0v.s2.057918af09ab from=translated src=- shape=4b736592 vocab=cd46845b
-/
theorem witnessChart1_f0EncoderB : f0EncoderB witnessChart1 = theta1K := by
  change structuredToF0 (encoderB witnessChart1) = theta1K
  rw [witnessChart1_encoderB, structuredToF0_f0ToStructured]

/--
@isnad1 id=eq.0h0v.s2.a59521b6e395 from=translated src=- shape=4b736592 vocab=38c10eef
-/
theorem witnessChartM_f0EncoderA : f0EncoderA witnessChartM = thetaMF := by
  change structuredToF0 (encoderA witnessChartM) = thetaMF
  rw [witnessChartM_encoderA, structuredToF0_f0ToStructured]

/--
@isnad1 id=eq.0h0v.s2.92f0ea163210 from=translated src=- shape=4b736592 vocab=cf5c7b96
-/
theorem witnessChartM_f0EncoderB : f0EncoderB witnessChartM = thetaMK := by
  change structuredToF0 (encoderB witnessChartM) = thetaMK
  rw [witnessChartM_encoderB, structuredToF0_f0ToStructured]

end AlbertLean.Generic.WitnessChart
