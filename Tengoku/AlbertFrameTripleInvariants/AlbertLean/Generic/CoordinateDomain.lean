import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParameterFamily
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FullOrbitFibre

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The explicit fixed-moment coordinate domain

All non-residual chart coordinates and the residual matrix moment are fixed
to the accepted first witness. Both determinant roots are nonzero, but their
sum is allowed to vary. Membership is given by matrix equations and
nonvanishing conditions, without any orbit predicate in its definition.

Every member has an actual full Albert automorphism to its normalized
parameter representative. No arbitrary-frame coverage theorem is asserted.
-/

noncomputable section

namespace AlbertLean.Generic.CoordinateDomain

open AlbertLean
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.FullOrbitFibre
open AlbertLean.Generic.LawfulChart
open AlbertLean.Generic.ParameterFamily
open AlbertLean.Generic.WitnessChart
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.NormalizedOrbitSection

/-- Open residual pairs with the displayed fixed matrix moment.-/
def FixedMomentPair (Q : ResidualPair ℚ) : Prop :=
  ResidualOpen Q ∧ moment Q = parameterMoment

/-- Insert the variable residual pair into the literal retained witness chart.-/
def coordinateTriple (Q : ResidualPair ℚ) : WitnessTriple :=
  fibreTriple witnessChart1 Q

/--
@isnad1 id=fixedmom.1h1v.s3.5f4d599bde68 from=translated src=- shape=da80b8de vocab=3df4b53c
-/
theorem parameterResidualPair_fixedMoment (t : ℚ) (ht : t ≠ 0) :
    FixedMomentPair (parameterResidualPair t ht) :=
  ⟨parameterResidualPair_open t ht, parameterResidualPair_moment t ht⟩

/--
@isnad1 id=eq.1h1v.s4.73a9503e03c1 from=translated src=- shape=7f4b6afe vocab=07c398c6
-/
@[simp] theorem coordinateTriple_parameter (t : ℚ) (ht : t ≠ 0) :
    coordinateTriple (parameterResidualPair t ht) = parameterTriple t ht := rfl

/-- The fixed determinant of the moment is the product of the actual roots.
@isnad1 id=eq.1h1v.s4.68ee9d818718 from=translated src=- shape=d5974ed6 vocab=ff28fa06
-/
theorem fixedMoment_deltaStar (Q : ResidualPair ℚ) (hQ : FixedMomentPair Q) :
    deltaStar Q = witnessScale / delta Q := by
  apply (eq_div_iff hQ.1.1).mpr
  change Matrix.det Q.A * Matrix.det Q.X = witnessScale
  rw [← Matrix.det_mul]
  change Matrix.det (moment Q) = witnessScale
  rw [hQ.2, parameterMoment_det]

/--
@isnad1 id=eq.1h1v.s5.335a721e5e5a from=translated src=- shape=a1242942 vocab=865c4d9a
-/
theorem fixedMoment_baseRootSum (Q : ResidualPair ℚ)
    (hQ : FixedMomentPair Q) :
    baseRootSum Q = delta Q + witnessScale / delta Q := by
  rw [baseRootSum, fixedMoment_deltaStar Q hQ]

/-- The scalar parameter is the actual vector determinant, and the
normalizing transporter is a proved unital product automorphism.
@isnad1 id=fullrela.1h1v.s4.fce0c0190d8f from=translated src=- shape=380dfb5f vocab=dc123457
-/
theorem coordinateTriple_normalForm (Q : ResidualPair ℚ)
    (hQ : FixedMomentPair Q) :
    FullRelated (parameterTriple (delta Q) hQ.1.1) (coordinateTriple Q) := by
  have hrel : Related
      (residualPairOfChart (parameterChart (delta Q) hQ.1.1)) Q := by
    rw [parameterChart_residualPair]
    apply (related_iff_same_moment_delta _ _
      ((parameterResidualPair_open (delta Q) hQ.1.1).1) hQ.1.1).mpr
    exact ⟨(parameterResidualPair_moment _ _).trans hQ.2.symm,
      parameterResidualPair_delta _ _⟩
  simpa only [parameterTriple, coordinateTriple, fibreTriple,
    parameterChart, chartWithResidualPair_reinsert] using
    fullRelated_of_related (parameterChart (delta Q) hQ.1.1) Q hrel

/-- All points of the displayed coordinate domain are lawful ordered frames.
@isnad1 id=lawfulfr.1h1v.s3.864aa2bc2d22 from=translated src=- shape=80a4b622 vocab=d533091c
-/
theorem coordinateTriple_lawful (Q : ResidualPair ℚ)
    (hQ : FixedMomentPair Q) : LawfulFrameTriple (coordinateTriple Q) := by
  rcases coordinateTriple_normalForm Q hQ with ⟨g, hg⟩
  exact (lawfulFrameTriple_iff_of_transports g _ _ hg).mpr
    (parameterTriple_lawful (delta Q) hQ.1.1)

/--
@isnad1 id=eq.1h1v.s4.2bcfe8b2bd22 from=translated src=- shape=76a0fb63 vocab=412942e1
-/
theorem coordinateTriple_ledger_normalForm (Q : ResidualPair ℚ)
    (hQ : FixedMomentPair Q) :
    ledger (coordinateTriple Q) = ledger (parameterTriple (delta Q) hQ.1.1) :=
  (coordinateTriple_normalForm Q hQ).ledger_eq.symm

/--
@isnad1 id=eq.1h1v.s4.ac605f221f9c from=translated src=- shape=0135e4ff vocab=acc7c743
-/
theorem coordinateTriple_detector_normalForm (Q : ResidualPair ℚ)
    (hQ : FixedMomentPair Q) :
    traceCubeDetector (coordinateTriple Q) =
      traceCubeDetector (parameterTriple (delta Q) hQ.1.1) :=
  (coordinateTriple_normalForm Q hQ).traceCubeDetector_eq.symm

end AlbertLean.Generic.CoordinateDomain
