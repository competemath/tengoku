import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FrameTransport
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.LawfulChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Full automorphism classes inside a fixed explicit residual fibre

The residual two-family cover supplies actual Albert automorphisms. When
the two representatives have different trace-cube detector values, invariance
under every `JordanAut` prevents any further identification. Thus the detector
is a complete invariant on this fibre. This concerns the restriction of full
automorphism equivalence to these points; it does not assert that the fibre
is stable under all automorphisms, or that arbitrary triples have this chart.

On such a two-class fibre every rational-valued invariant is affine in the
detector. This is two-point interpolation, with no claim about a global
invariant ring or exceptional specificity.
-/

noncomputable section

namespace AlbertLean.Generic.FullOrbitFibre

open AlbertLean
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.LawfulChart
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction

/-- The ordered public triple obtained by replacing only the residual pair.-/
def fibreTriple (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ) : WitnessTriple :=
  chartWitnessTriple (chartWithResidualPair x Q)

/-- Membership in the open residual base fibre, with all other chart fields fixed.-/
def InFibre (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ) : Prop :=
  ResidualOpen Q ∧ sameResidualBase (residualPairOfChart x) Q

/-- Residual transport gives a full unital product automorphism of public triples.-/
theorem fullRelated_of_related (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (h : Related (residualPairOfChart x) Q) :
    FullRelated (chartWitnessTriple x) (fibreTriple x Q) := by
  rcases h with ⟨G, hG⟩
  have heq : chartWithResidualPair x Q = actChart G x := by
    rw [← hG, ← residualPairOfChart_actChart]
    change chartWithResidualPair (actChart G x)
      (residualPairOfChart (actChart G x)) = actChart G x
    exact chartWithResidualPair_self _
  refine ⟨ResidualAction.jordanAut G, ?_⟩
  unfold fibreTriple
  rw [heq]
  exact jordanAut_chartWitnessTriple_actChart G x

/-- Every point of the fixed open fibre belongs to one of two full classes.-/
theorem fullRelated_cover (x : ExplicitFrameChart ℚ)
    (hx : ResidualOpen (residualPairOfChart x)) (Q : ResidualPair ℚ)
    (hQ : InFibre x Q) :
    FullRelated (chartWitnessTriple x) (fibreTriple x Q) ∨
      FullRelated (chartWitnessTriple (rootSwappedChart x hx)) (fibreTriple x Q) := by
  rcases (sameResidualBase_iff_related_or_swapped
    (residualPairOfChart x) hx Q hQ.1).mp hQ.2 with h | h
  · exact Or.inl (fullRelated_of_related x Q h)
  · apply Or.inr
    have hs : Related (residualPairOfChart (rootSwappedChart x hx)) Q := by
      simpa [rootSwappedChart] using h
    simpa [fibreTriple, rootSwappedChart] using
      fullRelated_of_related (rootSwappedChart x hx) Q hs

/-- The original residual point is in its own open fibre.-/
theorem original_inFibre (x : ExplicitFrameChart ℚ)
    (hx : ResidualOpen (residualPairOfChart x)) :
    InFibre x (residualPairOfChart x) := ⟨hx, rfl, rfl⟩

/-- The genuine root-swapped representative belongs to the same open fibre.-/
theorem swapped_inFibre (x : ExplicitFrameChart ℚ)
    (hx : ResidualOpen (residualPairOfChart x)) :
    InFibre x (rootSwappedRepresentative (residualPairOfChart x) hx) :=
  ⟨rootSwappedRepresentative_open _ hx,
    rootSwappedRepresentative_baseMoment _ hx,
    rootSwappedRepresentative_baseRootSum _ hx⟩

/-- Frame lawfulness propagates across the entire fixed fibre.-/
theorem lawful_of_inFibre (x : ExplicitFrameChart ℚ)
    (hx : LawfulFrameTriple (chartWitnessTriple x)) (Q : ResidualPair ℚ)
    (hQ : InFibre x Q) : LawfulFrameTriple (fibreTriple x Q) :=
  (lawfulFrameTriple_chartWithResidualPair_iff_of_sameResidualBase x Q hQ.2).mpr hx

/-- A two-class cover separated by an invariant makes that invariant complete.-/
theorem fullRelated_iff_detector_of_cover {X₀ X₁ Y Z : WitnessTriple}
    (hsep : traceCubeDetector X₀ ≠ traceCubeDetector X₁)
    (hY : FullRelated X₀ Y ∨ FullRelated X₁ Y)
    (hZ : FullRelated X₀ Z ∨ FullRelated X₁ Z) :
    FullRelated Y Z ↔ traceCubeDetector Y = traceCubeDetector Z := by
  constructor
  · exact FullRelated.traceCubeDetector_eq
  · intro heq
    rcases hY with hY | hY <;> rcases hZ with hZ | hZ
    · exact hY.symm.trans hZ
    · exact (hsep (hY.traceCubeDetector_eq.trans
        (heq.trans hZ.traceCubeDetector_eq.symm))).elim
    · exact (hsep (hZ.traceCubeDetector_eq.trans
        (heq.symm.trans hY.traceCubeDetector_eq.symm))).elim
    · exact hY.symm.trans hZ

/-- On a detector-separated fixed fibre, detector equality is equivalent to
transport by a full Albert automorphism, even one outside the residual subgroup.-/
theorem fullRelated_iff_detector (x : ExplicitFrameChart ℚ)
    (hx : ResidualOpen (residualPairOfChart x))
    (hsep : traceCubeDetector (chartWitnessTriple x) ≠
      traceCubeDetector (chartWitnessTriple (rootSwappedChart x hx)))
    (Q R : ResidualPair ℚ) (hQ : InFibre x Q) (hR : InFibre x R) :
    FullRelated (fibreTriple x Q) (fibreTriple x R) ↔
      traceCubeDetector (fibreTriple x Q) = traceCubeDetector (fibreTriple x R) :=
  fullRelated_iff_detector_of_cover hsep
    (fullRelated_cover x hx Q hQ) (fullRelated_cover x hx R hR)

/-- Separation anywhere in a fixed fibre proves separation of its canonical
representatives. This permits reuse of an exact witness without computing an inverse.-/
theorem representative_separation_of_witness (x : ExplicitFrameChart ℚ)
    (hx : ResidualOpen (residualPairOfChart x)) (Q : ResidualPair ℚ)
    (hQ : InFibre x Q)
    (hsep : traceCubeDetector (chartWitnessTriple x) ≠
      traceCubeDetector (fibreTriple x Q)) :
    traceCubeDetector (chartWitnessTriple x) ≠
      traceCubeDetector (chartWitnessTriple (rootSwappedChart x hx)) := by
  rcases fullRelated_cover x hx Q hQ with h | h
  · exact (hsep h.traceCubeDetector_eq).elim
  · intro heq
    exact hsep (heq.trans h.traceCubeDetector_eq)

/-- The normalized detector is a literal rational bit on a separated fibre.-/
def detectorBit (X₀ X₁ Y : WitnessTriple) : ℚ :=
  (traceCubeDetector Y - traceCubeDetector X₀) /
    (traceCubeDetector X₁ - traceCubeDetector X₀)

theorem detectorBit_zero_or_one {X₀ X₁ Y : WitnessTriple}
    (hsep : traceCubeDetector X₀ ≠ traceCubeDetector X₁)
    (hY : FullRelated X₀ Y ∨ FullRelated X₁ Y) :
    detectorBit X₀ X₁ Y = 0 ∨ detectorBit X₀ X₁ Y = 1 := by
  have hd : traceCubeDetector X₁ - traceCubeDetector X₀ ≠ 0 :=
    sub_ne_zero.mpr hsep.symm
  rcases hY with h | h
  · left
    simp [detectorBit, ← h.traceCubeDetector_eq]
  · right
    simp [detectorBit, ← h.traceCubeDetector_eq, hd]

/-- Any rational-valued function constant on full automorphism classes is
two-point interpolation in the detector on the supplied two-class cover.-/
theorem invariant_affine_in_detector {X₀ X₁ Y : WitnessTriple}
    (hsep : traceCubeDetector X₀ ≠ traceCubeDetector X₁)
    (hY : FullRelated X₀ Y ∨ FullRelated X₁ Y)
    (f : WitnessTriple → ℚ)
    (hf : ∀ {U V}, FullRelated U V → f U = f V) :
    f Y = f X₀ + (f X₁ - f X₀) * detectorBit X₀ X₁ Y := by
  have hd : traceCubeDetector X₁ - traceCubeDetector X₀ ≠ 0 :=
    sub_ne_zero.mpr hsep.symm
  rcases hY with h | h
  · simp [detectorBit, ← h.traceCubeDetector_eq, ← hf h]
  · simp [detectorBit, ← h.traceCubeDetector_eq, ← hf h, hd]

/-- Exactly two induced full-automorphism classes in this lawful fixed fibre:
both representatives occur, every point is lawful and covered, the classes
are disjoint, and detector equality decides equivalence of any two points.-/
theorem lawfulFibre_two_full_classes (x : ExplicitFrameChart ℚ)
    (hx : ResidualOpen (residualPairOfChart x))
    (hlaw : LawfulFrameTriple (chartWitnessTriple x))
    (hsep : traceCubeDetector (chartWitnessTriple x) ≠
      traceCubeDetector (chartWitnessTriple (rootSwappedChart x hx))) :
    InFibre x (residualPairOfChart x) ∧
    InFibre x (rootSwappedRepresentative (residualPairOfChart x) hx) ∧
    ¬ FullRelated (chartWitnessTriple x)
      (chartWitnessTriple (rootSwappedChart x hx)) ∧
    (∀ Q, InFibre x Q → LawfulFrameTriple (fibreTriple x Q) ∧
      (FullRelated (chartWitnessTriple x) (fibreTriple x Q) ∨
       FullRelated (chartWitnessTriple (rootSwappedChart x hx)) (fibreTriple x Q))) ∧
    (∀ Q R, InFibre x Q → InFibre x R →
      (FullRelated (fibreTriple x Q) (fibreTriple x R) ↔
       traceCubeDetector (fibreTriple x Q) = traceCubeDetector (fibreTriple x R))) := by
  exact ⟨original_inFibre x hx, swapped_inFibre x hx,
    not_fullRelated_of_traceCubeDetector_ne hsep,
    fun Q hQ => ⟨lawful_of_inFibre x hlaw Q hQ, fullRelated_cover x hx Q hQ⟩,
    fun Q R hQ hR => fullRelated_iff_detector x hx hsep Q R hQ hR⟩

end AlbertLean.Generic.FullOrbitFibre
