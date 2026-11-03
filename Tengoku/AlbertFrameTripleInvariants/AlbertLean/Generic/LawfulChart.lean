import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualActionChartF0
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.FrameLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms equationsVanish_iff_lawfulEncoders` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms equationsVanish_iff_lawfulFrameTriple` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms explicitFrameEquationValues_chartWithResidualPair_of_moment_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms lawfulFrameTriple_chartWithResidualPair_iff_of_sameResidualBase` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rootSwappedChart_lawfulFrameTriple_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms jordanAut_chartWitnessTriple_actChart` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms equationsVanish_actChart_iff` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Lawful ordered frames on the explicit residual chart

The six explicit chart equations are exactly the `LawfulEncoder` conditions
for the two public F0 chart values.  Adjoining the fixed diagonal encoder
`diag(-1,0,1)` therefore gives an ordered `WitnessTriple` whose three entries
are lawful frames precisely when those equations vanish.

The residual chart action preserves this condition and transports the ordered
triple by the already constructed `JordanAut`.  This remains a statement about
members of `ExplicitFrameChart`; it makes no primitive-frame, chart-coverage,
or global-orbit claim.  The stored `kappa` coordinate is not constrained by
lawfulness.
-/

noncomputable section

namespace AlbertLean.Generic.LawfulChart

open AlbertLean
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.ResidualAction
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic

/-- The fixed first encoder, in the public F0 coordinates.-/
def chartBaseEncoder : Coord :=
  f0Diagonal (-1) 0 1

/-- The fixed chart encoder is the accepted literal `theta1E` value.
@isnad1 id=eq.0h0v.s2.6505dc713744 from=translated src=- shape=54c8eceb vocab=5e68dec7
-/
theorem chartBaseEncoder_eq_theta1E : chartBaseEncoder = theta1E := by
  funext i
  fin_cases i <;>
    norm_num [chartBaseEncoder, f0Diagonal, structuredEquiv,
      structuredToF0, diagonal, theta1E, q]

/-- The fixed diagonal encoder has trace, quadratic spur and cubic norm `(0,-1,0)`, respectively.
@isnad1 id=lawfulen.0h0v.s1.d76cfd0dcef7 from=translated src=- shape=49959d42 vocab=7e4bbc06
-/
theorem chartBaseEncoder_lawfulEncoder : LawfulEncoder chartBaseEncoder := by
  unfold LawfulEncoder chartBaseEncoder f0Diagonal
  rw [← sourceTrace_agrees_with_f0,
    ← sourceSpur_agrees_with_f0,
    ← sourceNorm_agrees_with_f0]
  simpa using
    (source_diagonal_restrictions (-1 : ℚ) (0 : ℚ) (1 : ℚ))

/-- All three ordered projectors of the fixed diagonal encoder satisfy the
public frame laws.
@isnad1 id=lawfulfr.0h0v.s1.99b16299a1e1 from=translated src=- shape=49959d42 vocab=153e186c
-/
theorem chartBaseEncoder_lawfulFrame : LawfulFrame chartBaseEncoder :=
  lawfulFrame_of_lawfulEncoder chartBaseEncoder
    chartBaseEncoder_lawfulEncoder

/-- The ordered public triple represented by a chart: fixed diagonal first,
then the chart's first and second varying encoders.-/
def chartWitnessTriple (x : ExplicitFrameChart ℚ) : WitnessTriple :=
  ⟨chartBaseEncoder, f0EncoderA x, f0EncoderB x⟩

/-- The chart evaluation matrix is exactly the residual-pair moment.
@isnad1 id=eq.0h1v.s5.39a33c477559 from=translated src=- shape=022ef4a4 vocab=5967bb1a
-/
theorem matrixM_eq_moment_residualPairOfChart
    (x : ExplicitFrameChart ℚ) :
    matrixM x = moment (residualPairOfChart x) := by
  simpa [matrixM, residualPairOfChart, moment] using
    (momentMatrix_eq_AMatrix_mul_XMatrix x.s1 x.s2 x.c1 x.c2)

/-- Re-reading and reinserting a chart's own residual pair recovers the
entire chart, including all retained fields.
@isnad1 id=eq.0h1v.s4.05cb8edfce78 from=translated src=- shape=d0ec1b20 vocab=0f5646f4
-/
@[simp] theorem chartWithResidualPair_self
    (x : ExplicitFrameChart ℚ) :
    chartWithResidualPair x (residualPairOfChart x) = x := by
  apply ExplicitFrameChart.ext <;> try rfl

/-- A second residual reinsertion replaces the first one while retaining the
same non-residual chart fields.
@isnad1 id=eq.0h3v.s5.1fcdc414caaa from=translated src=- shape=5001c867 vocab=2189079c
-/
@[simp] theorem chartWithResidualPair_reinsert
    (x : ExplicitFrameChart ℚ) (P Q : ResidualPair ℚ) :
    chartWithResidualPair (chartWithResidualPair x P) Q =
      chartWithResidualPair x Q := rfl

/-- Replacing the residual row/column data without changing its moment keeps
all six explicit frame-equation values.
@isnad1 id=eq.1h2v.s5.32c8df132b25 from=translated src=- shape=cc6525f6 vocab=fa6dadf5
-/
theorem explicitFrameEquationValues_chartWithResidualPair_of_moment_eq
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hQ : moment Q = moment (residualPairOfChart x)) :
    explicitFrameEquationValues (chartWithResidualPair x Q) =
      explicitFrameEquationValues x := by
  have hM : matrixM (chartWithResidualPair x Q) = matrixM x := by
    calc
      matrixM (chartWithResidualPair x Q) =
          moment (residualPairOfChart (chartWithResidualPair x Q)) :=
        matrixM_eq_moment_residualPairOfChart _
      _ = moment Q := by rw [residualPairOfChart_chartWithResidualPair]
      _ = moment (residualPairOfChart x) := hQ
      _ = matrixM x := (matrixM_eq_moment_residualPairOfChart x).symm
  have hdiagA : (chartWithResidualPair x Q).diagA = x.diagA := rfl
  have hdiagB : (chartWithResidualPair x Q).diagB = x.diagB := rfl
  have hr1 : (chartWithResidualPair x Q).r1 = x.r1 := rfl
  have hz1 : (chartWithResidualPair x Q).z1 = x.z1 := rfl
  have hr2 : (chartWithResidualPair x Q).r2 = x.r2 := rfl
  have hz2 : (chartWithResidualPair x Q).z2 = x.z2 := rfl
  apply FrameEquationValues.ext <;>
    simp only [explicitFrameEquationValues, hdiagA, hdiagB,
      hr1, hz1, hr2, hz2, hM]

/-- Every residual pair over the same declared residual base has the same
six frame-equation values after reinsertion.
@isnad1 id=eq.1h2v.s5.801e86886660 from=translated src=- shape=df465c01 vocab=7ce1ded7
-/
theorem explicitFrameEquationValues_chartWithResidualPair_of_sameResidualBase
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hQ : sameResidualBase (residualPairOfChart x) Q) :
    explicitFrameEquationValues (chartWithResidualPair x Q) =
      explicitFrameEquationValues x := by
  apply explicitFrameEquationValues_chartWithResidualPair_of_moment_eq
  exact hQ.1

/-- Equation vanishing is constant on reinsertion from the same residual
base fibre.
@isnad1 id=iff.1h2v.s5.4e50f9464b3a from=translated src=- shape=92e84dbe vocab=c504b33e
-/
theorem equationsVanish_chartWithResidualPair_iff_of_sameResidualBase
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hQ : sameResidualBase (residualPairOfChart x) Q) :
    EquationsVanish
        (explicitFrameEquationValues (chartWithResidualPair x Q)) ↔
      EquationsVanish (explicitFrameEquationValues x) := by
  rw [explicitFrameEquationValues_chartWithResidualPair_of_sameResidualBase
    x Q hQ]

/-- The six explicit equations vanish exactly when both varying public F0
encoders are lawful.
@isnad1 id=iff.0h1v.s4.80c9ba063be1 from=translated src=- shape=833d8fba vocab=77561f81
-/
theorem equationsVanish_iff_lawfulEncoders
    (x : ExplicitFrameChart ℚ) :
    EquationsVanish (explicitFrameEquationValues x) ↔
      LawfulEncoder (f0EncoderA x) ∧ LawfulEncoder (f0EncoderB x) := by
  rw [equationsVanish_iff_source_fixedSpectrum]
  unfold LawfulEncoder f0EncoderA f0EncoderB
  rw [← sourceTrace_agrees_with_f0,
    ← sourceSpur_agrees_with_f0,
    ← sourceNorm_agrees_with_f0,
    ← sourceTrace_agrees_with_f0,
    ← sourceSpur_agrees_with_f0,
    ← sourceNorm_agrees_with_f0]
  constructor
  · rintro ⟨hTa, hSa, hNa, hTb, hSb, hNb⟩
    exact ⟨⟨hTa, hSa, hNa⟩, ⟨hTb, hSb, hNb⟩⟩
  · rintro ⟨⟨hTa, hSa, hNa⟩, ⟨hTb, hSb, hNb⟩⟩
    exact ⟨hTa, hSa, hNa, hTb, hSb, hNb⟩

/-- Vanishing of the explicit equations is equivalent to lawfulness of every
ordered frame in the chart triple.  The forward direction obtains all three
projectors of each member from `lawfulFrame_of_lawfulEncoder`; the converse
uses the two varying members in their fixed order.
@isnad1 id=iff.0h1v.s4.131808bda43d from=translated src=- shape=200b1af7 vocab=01e2c10e
-/
theorem equationsVanish_iff_lawfulFrameTriple
    (x : ExplicitFrameChart ℚ) :
    EquationsVanish (explicitFrameEquationValues x) ↔
      LawfulFrameTriple (chartWitnessTriple x) := by
  constructor
  · intro hx r
    have hAB := (equationsVanish_iff_lawfulEncoders x).mp hx
    fin_cases r
    · exact chartBaseEncoder_lawfulFrame
    · exact lawfulFrame_of_lawfulEncoder (f0EncoderA x) hAB.1
    · exact lawfulFrame_of_lawfulEncoder (f0EncoderB x) hAB.2
  · intro hx
    apply (equationsVanish_iff_lawfulEncoders x).mpr
    have hA := (hx (1 : Fin 3)).1
    have hB := (hx (2 : Fin 3)).1
    exact ⟨hA, hB⟩

/-- Lawfulness of the full ordered public triple is constant on the same
residual base fibre.
@isnad1 id=iff.1h2v.s4.d4a0703c1d7c from=translated src=- shape=c0bba286 vocab=f836c24a
-/
theorem lawfulFrameTriple_chartWithResidualPair_iff_of_sameResidualBase
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hQ : sameResidualBase (residualPairOfChart x) Q) :
    LawfulFrameTriple (chartWitnessTriple (chartWithResidualPair x Q)) ↔
      LawfulFrameTriple (chartWitnessTriple x) := by
  rw [← equationsVanish_iff_lawfulFrameTriple,
    equationsVanish_chartWithResidualPair_iff_of_sameResidualBase x Q hQ,
    equationsVanish_iff_lawfulFrameTriple]

/-- Reinsert the genuine normalized-section root-swapped residual
representative into the chart.-/
def rootSwappedChart (x : ExplicitFrameChart ℚ)
    (hP : ResidualOpen (residualPairOfChart x)) : ExplicitFrameChart ℚ :=
  chartWithResidualPair x
    (rootSwappedRepresentative (residualPairOfChart x) hP)

/-- The genuine normalized root-swapped representative has the same six
frame-equation values as the original chart.
@isnad1 id=eq.1h1v.s4.4f6b9d123c50 from=translated src=- shape=f966e56a vocab=a3b41d19
-/
theorem rootSwappedChart_equationValues
    (x : ExplicitFrameChart ℚ)
    (hP : ResidualOpen (residualPairOfChart x)) :
    explicitFrameEquationValues (rootSwappedChart x hP) =
      explicitFrameEquationValues x := by
  apply explicitFrameEquationValues_chartWithResidualPair_of_moment_eq
  simpa [baseMoment] using
    (rootSwappedRepresentative_baseMoment (residualPairOfChart x) hP)

/-- The six equations vanish on the normalized root-swapped chart exactly
when they vanish on the original chart.
@isnad1 id=iff.1h1v.s5.91aad2512e97 from=translated src=- shape=5e053d5f vocab=463ff399
-/
theorem rootSwappedChart_equationsVanish_iff
    (x : ExplicitFrameChart ℚ)
    (hP : ResidualOpen (residualPairOfChart x)) :
    EquationsVanish (explicitFrameEquationValues (rootSwappedChart x hP)) ↔
      EquationsVanish (explicitFrameEquationValues x) := by
  rw [rootSwappedChart_equationValues]

/-- The normalized root-swapped chart carries a lawful ordered public frame
triple exactly when the original chart does.
@isnad1 id=iff.1h1v.s4.64c3c0f56552 from=translated src=- shape=229bfc55 vocab=4aa1c7da
-/
theorem rootSwappedChart_lawfulFrameTriple_iff
    (x : ExplicitFrameChart ℚ)
    (hP : ResidualOpen (residualPairOfChart x)) :
    LawfulFrameTriple (chartWitnessTriple (rootSwappedChart x hP)) ↔
      LawfulFrameTriple (chartWitnessTriple x) := by
  rw [← equationsVanish_iff_lawfulFrameTriple,
    rootSwappedChart_equationsVanish_iff,
    equationsVanish_iff_lawfulFrameTriple]

/-- The actual residual Albert automorphism carries all three ordered entries
of the chart triple to the transformed chart triple.
@isnad1 id=transpor.0h2v.s4.95d84f2c6960 from=translated src=- shape=71e2454d vocab=6c84c3cd
-/
theorem jordanAut_chartWitnessTriple_actChart
    (G : DetOneMatrix ℚ) (x : ExplicitFrameChart ℚ) :
    Transports (jordanAut G) (chartWitnessTriple x)
      (chartWitnessTriple (actChart G x)) := by
  exact ⟨jordanAut_f0Diagonal G (-1) 0 1,
    jordanAut_encoderA_actChart G x,
    jordanAut_encoderB_actChart G x⟩

/-- The quadratic source spur is invariant under the residual action.
@isnad1 id=eq.0h2v.s4.e56c2a44684f from=translated src=- shape=f6201726 vocab=fbd539de
-/
theorem sourceSpur_act
    (G : DetOneMatrix ℚ) (y : JCoord ℚ) :
    sourceSpur (act G y) = sourceSpur y := by
  simp only [sourceSpur, AlbertLean.Generic.ResidualAction.act]
  rw [nV_actV G, nS_actS G, nC_actC G]

/-- Residual chart transport preserves, in both directions, simultaneous
vanishing of the six fixed-spectrum equations.
@isnad1 id=iff.0h2v.s4.782c8e72e9aa from=translated src=- shape=3fd99407 vocab=81a3a302
-/
theorem equationsVanish_actChart_iff
    (G : DetOneMatrix ℚ) (x : ExplicitFrameChart ℚ) :
    EquationsVanish (explicitFrameEquationValues (actChart G x)) ↔
      EquationsVanish (explicitFrameEquationValues x) := by
  rw [equationsVanish_iff_source_fixedSpectrum,
    equationsVanish_iff_source_fixedSpectrum,
    encoderA_actChart, encoderB_actChart,
    sourceTrace_act, sourceSpur_act, sourceNorm_act,
    sourceTrace_act, sourceSpur_act, sourceNorm_act]

/-- Equivalently, the ordered public frame triple remains lawful exactly
along the residual chart action.
@isnad1 id=iff.0h2v.s4.1067a0773870 from=translated src=- shape=34fa42c5 vocab=de6d5725
-/
theorem lawfulFrameTriple_actChart_iff
    (G : DetOneMatrix ℚ) (x : ExplicitFrameChart ℚ) :
    LawfulFrameTriple (chartWitnessTriple (actChart G x)) ↔
      LawfulFrameTriple (chartWitnessTriple x) := by
  rw [← equationsVanish_iff_lawfulFrameTriple,
    equationsVanish_actChart_iff,
    equationsVanish_iff_lawfulFrameTriple]

end AlbertLean.Generic.LawfulChart
