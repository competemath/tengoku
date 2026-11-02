import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.NormalizedOrbitSection
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.SectionFibre

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @ResidualSL4BaseFibreTwoOrbitTheorem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ResidualSL4BaseFibreTwoOrbitTheorem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Two explicit action-related families in a residual base fibre

This module relates the explicit determinant-one action on residual matrix
pairs to the accepted normalized-section root swap and two-point fibre.  On
the open where both actual determinant roots are nonzero, a branch-free fibre
of the declared residual base `(A * X, det X + det A)` is the disjoint union
of two displayed existential `Related` families.

This is a chart-local theorem about explicit `4 x 4` matrix pairs.  It does
not construct a quotient, prove a global deck action, identify a split Albert
algebra or frame space, or establish an invariant-field or physics result.
-/

namespace AlbertLean.Residual.ResidualTwoOrbit

open Matrix
open AlbertLean.Residual.SL4PairAction

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The explicit open where both actual determinant roots are nonzero.-/
def ResidualOpen (P : ResidualPair K) : Prop :=
  delta P ≠ 0 ∧ deltaStar P ≠ 0

/-- The matrix coordinate retained by the declared residual base.-/
def baseMoment (P : ResidualPair K) : Mat4 K :=
  moment P

/-- The sum of the two actual determinant roots retained by the base.-/
def baseRootSum (P : ResidualPair K) : K :=
  delta P + deltaStar P

/-- Equality in the declared explicit residual base.-/
def sameResidualBase (P Q : ResidualPair K) : Prop :=
  baseMoment Q = baseMoment P ∧ baseRootSum Q = baseRootSum P

/-- Convert an open residual pair to the accepted normalized-section record.
The nonvanishing of `det M` is derived from the two actual determinant roots.-/
def sectionOfResidualPair (P : ResidualPair K) (hP : ResidualOpen P) :
    AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection K where
  M := moment P
  Delta := delta P
  Delta_ne_zero := hP.1
  detM_ne_zero := by
    rw [moment, Matrix.det_mul]
    exact mul_ne_zero hP.2 hP.1

/-- Convert a normalized-section point to its displayed residual matrix pair.-/
def residualPairOfSection
    (s : AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection K) :
    ResidualPair K where
  A := AlbertLean.Residual.NormalizedRootSwap.A0 s
  X := AlbertLean.Residual.NormalizedRootSwap.X0 s

/-- The displayed residual representative obtained by exchanging the actual
normalized-section determinant root.-/
def rootSwappedRepresentative (P : ResidualPair K) (hP : ResidualOpen P) :
    ResidualPair K :=
  residualPairOfSection
    (AlbertLean.Residual.NormalizedRootSwap.rootSwap
      (sectionOfResidualPair P hP))

@[simp] theorem sectionOfResidualPair_M (P : ResidualPair K)
    (hP : ResidualOpen P) :
    (sectionOfResidualPair P hP).M = moment P := rfl

@[simp] theorem sectionOfResidualPair_Delta (P : ResidualPair K)
    (hP : ResidualOpen P) :
    (sectionOfResidualPair P hP).Delta = delta P := rfl

@[simp] theorem sectionOfResidualPair_DeltaStar (P : ResidualPair K)
    (hP : ResidualOpen P) :
    AlbertLean.Residual.NormalizedRootSwap.DeltaStar
      (sectionOfResidualPair P hP) = deltaStar P := by
  apply (div_eq_iff hP.1).2
  simp [sectionOfResidualPair, moment, delta, deltaStar, Matrix.det_mul]

@[simp] theorem sectionOfResidualPair_Sb (P : ResidualPair K)
    (hP : ResidualOpen P) :
    AlbertLean.Residual.NormalizedRootSwap.Sb
      (sectionOfResidualPair P hP) = baseRootSum P := by
  simp [AlbertLean.Residual.NormalizedRootSwap.Sb, baseRootSum]

@[simp] theorem residualPairOfSection_moment
    (s : AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection K) :
    moment (residualPairOfSection s) = s.M := by
  exact AlbertLean.Residual.NormalizedRootSwap.A0_mul_X0 s

@[simp] theorem residualPairOfSection_delta
    (s : AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection K) :
    delta (residualPairOfSection s) = s.Delta := by
  exact AlbertLean.Residual.NormalizedRootSwap.det_X0 s

@[simp] theorem residualPairOfSection_deltaStar
    (s : AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection K) :
    deltaStar (residualPairOfSection s) =
      AlbertLean.Residual.NormalizedRootSwap.DeltaStar s := by
  exact AlbertLean.Residual.NormalizedRootSwap.det_A0 s

theorem residualPairOfSection_open
    (s : AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection K) :
    ResidualOpen (residualPairOfSection s) := by
  constructor
  · simpa using s.Delta_ne_zero
  · rw [residualPairOfSection_deltaStar]
    exact div_ne_zero s.detM_ne_zero s.Delta_ne_zero

@[simp] theorem section_residual_roundtrip
    (s : AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection K) :
    sectionOfResidualPair (residualPairOfSection s)
      (residualPairOfSection_open s) = s := by
  apply AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection.ext
  · exact residualPairOfSection_moment s
  · exact residualPairOfSection_delta s

theorem sameResidualBase_to_sectionSameBase
    (P Q : ResidualPair K) (hP : ResidualOpen P) (hQ : ResidualOpen Q)
    (hbase : sameResidualBase P Q) :
    AlbertLean.Residual.SectionFibre.SameBase (sectionOfResidualPair P hP)
      (sectionOfResidualPair Q hQ) := by
  exact ⟨hbase.1, by simpa using hbase.2⟩

@[simp] theorem rootSwappedRepresentative_delta
    (P : ResidualPair K) (hP : ResidualOpen P) :
    delta (rootSwappedRepresentative P hP) = deltaStar P := by
  simp [rootSwappedRepresentative]

@[simp] theorem rootSwappedRepresentative_deltaStar
    (P : ResidualPair K) (hP : ResidualOpen P) :
    deltaStar (rootSwappedRepresentative P hP) = delta P := by
  simp [rootSwappedRepresentative]

@[simp] theorem rootSwappedRepresentative_baseMoment
    (P : ResidualPair K) (hP : ResidualOpen P) :
    baseMoment (rootSwappedRepresentative P hP) = baseMoment P := by
  simp [rootSwappedRepresentative, baseMoment]

@[simp] theorem rootSwappedRepresentative_baseRootSum
    (P : ResidualPair K) (hP : ResidualOpen P) :
    baseRootSum (rootSwappedRepresentative P hP) = baseRootSum P := by
  simp [baseRootSum, add_comm]

theorem rootSwappedRepresentative_open
    (P : ResidualPair K) (hP : ResidualOpen P) :
    ResidualOpen (rootSwappedRepresentative P hP) := by
  constructor <;> simp [hP.1, hP.2]

theorem not_related_rootSwappedRepresentative
    (P : ResidualPair K) (hP : ResidualOpen P)
    (hbranch : delta P ≠ deltaStar P) :
    ¬ Related P (rootSwappedRepresentative P hP) := by
  intro h
  apply hbranch
  simpa using (related_preserves_invariants h).2.1

theorem rootSwappedRepresentative_not_related
    (P : ResidualPair K) (hP : ResidualOpen P)
    (hbranch : delta P ≠ deltaStar P) :
    ¬ Related (rootSwappedRepresentative P hP) P := by
  intro h
  apply hbranch
  simpa using (related_preserves_invariants h).2.1.symm

theorem related_families_disjoint
    (P : ResidualPair K) (hP : ResidualOpen P)
    (hbranch : delta P ≠ deltaStar P) (Q : ResidualPair K) :
    ¬ (Related P Q ∧ Related (rootSwappedRepresentative P hP) Q) := by
  rintro ⟨hPQ, hSQ⟩
  apply hbranch
  calc
    delta P = delta Q := (related_preserves_invariants hPQ).2.1
    _ = delta (rootSwappedRepresentative P hP) :=
      (related_preserves_invariants hSQ).2.1.symm
    _ = deltaStar P := rootSwappedRepresentative_delta P hP

theorem sameResidualBase_iff_related_or_swapped
    (P : ResidualPair K) (hP : ResidualOpen P)
    (Q : ResidualPair K) (hQ : ResidualOpen Q) :
    sameResidualBase P Q ↔
      Related P Q ∨ Related (rootSwappedRepresentative P hP) Q := by
  constructor
  · intro hbase
    have hsection := sameResidualBase_to_sectionSameBase P Q hP hQ hbase
    rcases (AlbertLean.Residual.SectionFibre.sameBase_iff_eq_or_eq_rootSwap
      (sectionOfResidualPair P hP) (sectionOfResidualPair Q hQ)).mp hsection with
      hsame | hswap
    · left
      apply (AlbertLean.Residual.NormalizedOrbitSection.related_iff_same_moment_delta
        P Q hP.1 hQ.1).2
      constructor
      · exact hbase.1.symm
      · have hDelta := congrArg
          AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection.Delta
          hsame
        simpa using hDelta.symm
    · right
      apply (AlbertLean.Residual.NormalizedOrbitSection.related_iff_same_moment_delta
        (rootSwappedRepresentative P hP) Q
        (rootSwappedRepresentative_open P hP).1 hQ.1).2
      constructor
      · calc
          moment (rootSwappedRepresentative P hP) = moment P := by
            simpa [baseMoment] using rootSwappedRepresentative_baseMoment P hP
          _ = moment Q := hbase.1.symm
      · have hDelta := congrArg
          AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection.Delta
          hswap
        simpa using hDelta.symm
  · rintro (hPQ | hSQ)
    · have h := related_preserves_invariants hPQ
      exact ⟨h.1.symm, by
        simp only [baseRootSum]
        rw [h.2.1, h.2.2]⟩
    · have h := related_preserves_invariants hSQ
      constructor
      · calc
          baseMoment Q = baseMoment (rootSwappedRepresentative P hP) := h.1.symm
          _ = baseMoment P := rootSwappedRepresentative_baseMoment P hP
      · calc
          baseRootSum Q = baseRootSum (rootSwappedRepresentative P hP) := by
            simp only [baseRootSum]
            rw [← h.2.1, ← h.2.2]
          _ = baseRootSum P := rootSwappedRepresentative_baseRootSum P hP

/-- on the explicit branch-free open,
the residual base fibre is exhausted by two disjoint displayed action-related
families represented by a pair and the normalized root-swapped pair.-/
theorem ResidualSL4BaseFibreTwoOrbitTheorem
    (P : ResidualPair K) (hP : ResidualOpen P)
    (hbranch : delta P ≠ deltaStar P) :
    let Pswap := rootSwappedRepresentative P hP
    delta Pswap = deltaStar P ∧
      deltaStar Pswap = delta P ∧
      baseMoment Pswap = baseMoment P ∧
      baseRootSum Pswap = baseRootSum P ∧
      ¬ Related P Pswap ∧
      ¬ Related Pswap P ∧
      (∀ Q : ResidualPair K,
        ¬ (Related P Q ∧ Related Pswap Q)) ∧
      ∀ Q : ResidualPair K, ResidualOpen Q →
        (sameResidualBase P Q ↔
          Related P Q ∨ Related Pswap Q) := by
  dsimp
  exact ⟨rootSwappedRepresentative_delta P hP,
    rootSwappedRepresentative_deltaStar P hP,
    rootSwappedRepresentative_baseMoment P hP,
    rootSwappedRepresentative_baseRootSum P hP,
    not_related_rootSwappedRepresentative P hP hbranch,
    rootSwappedRepresentative_not_related P hP hbranch,
    related_families_disjoint P hP hbranch,
    sameResidualBase_iff_related_or_swapped P hP⟩

end

end AlbertLean.Residual.ResidualTwoOrbit
