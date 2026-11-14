import Tengoku.TdaLib.TDA.Persistence.BoundaryPlanLaws
import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportForward
import Tengoku.TdaLib.TDA.Persistence.FiniteWeightedBoundaryTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Atomic finite weighted diagrams and boundary transport

Native finite weighted diagrams define positive atomic measures. Feasible
matrices give boundary plans of exactly the same powered cost, and every Borel
competitor between these atomic measures gives a matrix of no greater cost.
The two optimized values agree, and the native optimizer attains the all-plan
value. The comparison permits arbitrary diagonal endpoints and infinite costs.
-/
set_option autoImplicit false
noncomputable section
namespace TDA.Persistence.BoundaryTransport
open Set MeasureTheory
open scoped ENNReal NNReal Classical

/-- The exact positive atomic measure of a native finite weighted diagram.-/
def atomicMeasure (D : FiniteWeightedDiagram) : Measure Interior :=
  ∑ i : D.supportLabels, (D.weights i : ℝ≥0∞) • Measure.dirac i.1

/-- Pair of native support labels as an interior–interior boundary-plan point.-/
def directLeg {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) : PlanSpace :=
  ⟨(interiorIncl i.1, interiorIncl j.1), Or.inl i.1.2⟩

/-- Convert one feasible native weighted matrix into an actual Borel boundary plan.-/
def atomicBoundaryPlan (D E : FiniteWeightedDiagram)
    (a : FiniteWeightedBoundaryPlan D.weights E.weights) : Measure PlanSpace :=
  (∑ i : D.supportLabels, ∑ j : E.supportLabels,
    ENNReal.ofReal (a.mass i j) • Measure.dirac (directLeg i j)) +
  (∑ i : D.supportLabels,
    ENNReal.ofReal (a.deletionMass i) • Measure.dirac (deleteLeg i.1)) +
  ∑ j : E.supportLabels,
    ENNReal.ofReal (a.insertionMass j) • Measure.dirac (insertLeg j.1)

@[simp] theorem directLeg_firstFiber {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) (s : Set Interior) :
    directLeg i j ∈ firstFiber s ↔ i.1 ∈ s := by
  change interiorIncl i.1 ∈ interiorIncl '' s ↔ i.1 ∈ s
  constructor
  · rintro ⟨x, hx, heq⟩
    exact (interiorIncl_injective heq).symm ▸ hx
  · exact fun hi => ⟨i.1, hi, rfl⟩

@[simp] theorem directLeg_secondFiber {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) (s : Set Interior) :
    directLeg i j ∈ secondFiber s ↔ j.1 ∈ s := by
  change interiorIncl j.1 ∈ interiorIncl '' s ↔ j.1 ∈ s
  constructor
  · rintro ⟨x, hx, heq⟩
    exact (interiorIncl_injective heq).symm ▸ hx
  · exact fun hj => ⟨j.1, hj, rfl⟩

private theorem diagonalProjection_not_image (x : Interior) (s : Set Interior) :
    diagonalProjection x ∉ interiorIncl '' s := by
  rintro ⟨y, _, heq⟩
  have h : (diagonalProjection x).1.1 < (diagonalProjection x).1.2 := by
    rw [← heq]
    exact y.2
  simp [diagonalProjection] at h

@[simp] theorem deleteLeg_firstFiber (x : Interior) (s : Set Interior) :
    deleteLeg x ∈ firstFiber s ↔ x ∈ s := by
  change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (interiorIncl_injective heq).symm ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

@[simp] theorem insertLeg_secondFiber (x : Interior) (s : Set Interior) :
    insertLeg x ∈ secondFiber s ↔ x ∈ s := by
  change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (interiorIncl_injective heq).symm ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

@[simp] theorem insertLeg_not_firstFiber (x : Interior) (s : Set Interior) :
    insertLeg x ∉ firstFiber s := diagonalProjection_not_image x s

@[simp] theorem deleteLeg_not_secondFiber (x : Interior) (s : Set Interior) :
    deleteLeg x ∉ secondFiber s := diagonalProjection_not_image x s

theorem atomicMeasure_apply (D : FiniteWeightedDiagram) (s : Set Interior)
    (hs : MeasurableSet s) :
    atomicMeasure D s =
      ∑ i : D.supportLabels, if i.1 ∈ s then (D.weights i : ℝ≥0∞) else 0 := by
  simp [atomicMeasure, Set.indicator, hs]

theorem atomicMeasure_mass (D : FiniteWeightedDiagram) :
    atomicMeasure D Set.univ = ∑ i : D.supportLabels, (D.weights i : ℝ≥0∞) := by
  rw [atomicMeasure_apply D Set.univ MeasurableSet.univ]
  simp

theorem atomicMeasure_isFinite (D : FiniteWeightedDiagram) :
    IsFiniteMeasure (atomicMeasure D) := by
  refine ⟨?_⟩
  rw [atomicMeasure_mass]
  exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.coe_lt_top)

@[simp] theorem atomicMeasure_zero :
    atomicMeasure (0 : FiniteWeightedDiagram) = 0 := by
  simp [atomicMeasure]

/-- Coalesced native occurrences are represented by their single Finsupp atom mass.-/
theorem atomicMeasure_singleton (D : FiniteWeightedDiagram) (x : Interior) :
    atomicMeasure D {x} = (D x : ℝ≥0∞) := by
  rw [atomicMeasure_apply D {x} (measurableSet_singleton x)]
  by_cases hx : x ∈ D.support
  · let i : D.supportLabels := ⟨x, hx⟩
    rw [Finset.sum_eq_single i]
    · simp [i, FiniteWeightedDiagram.weights]
    · intro j _ hji
      have hne : j.1 ≠ x := by
        intro heq
        exact hji (Subtype.ext heq)
      simp [hne]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · have hzero : D x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i _
    have hne : i.1 ≠ x := by
      intro heq
      exact hx (heq ▸ i.2)
    simp [hne]

@[simp] theorem planPowerCost_directLeg (p : ℝ) {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) :
    planPowerCost p (directLeg i j) =
      ENNReal.ofReal ((finitePairCost (D.coordinates i) (E.coordinates j)).toReal ^ p) := by
  simp [planPowerCost, directLeg, interiorIncl, FiniteWeightedDiagram.coordinates,
    Subtype.dist_eq, finitePairCost_toReal, dist_eq_norm]

@[simp] theorem planPowerCost_deleteLeg (p : ℝ) (x : Interior) :
    planPowerCost p (deleteLeg x) =
      ENNReal.ofReal ((diagonalCost x.1).toReal ^ p) := by
  simp [planPowerCost, deleteLeg, deleteLeg_distance, depth]

@[simp] theorem planPowerCost_insertLeg (p : ℝ) (x : Interior) :
    planPowerCost p (insertLeg x) =
      ENNReal.ofReal ((diagonalCost x.1).toReal ^ p) := by
  simp [planPowerCost, insertLeg, insertLeg_distance, depth]

/-- Exact interior–interior cell for a pair of native support labels.-/
def atomicPairCell {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) : Set PlanSpace :=
  firstFiber {i.1} ∩ secondFiber {j.1}

theorem measurableSet_atomicPairCell {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) :
    MeasurableSet (atomicPairCell i j) :=
  (measurableSet_firstFiber (measurableSet_singleton i.1)).inter
    (measurableSet_secondFiber (measurableSet_singleton j.1))

/-- For a fixed source label, distinct target cells are disjoint.-/
private theorem atomicPairCell_disjoint_right {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) {j k : E.supportLabels} (hjk : j ≠ k) :
    Disjoint (atomicPairCell i j) (atomicPairCell i k) := by
  apply Set.disjoint_left.mpr
  intro z hzj hzk
  have hj : z ∈ secondFiber {j.1} := hzj.2
  have hk : z ∈ secondFiber {k.1} := hzk.2
  rcases hj with ⟨x, hx, heqj⟩
  rcases hk with ⟨y, hy, heqk⟩
  have hxy : x = y := interiorIncl_injective (heqj.trans heqk.symm)
  have hjk' : j.1 = k.1 := by simpa using hx.symm.trans (hxy.trans hy)
  exact hjk (Subtype.ext hjk')

/-- For a fixed target label, distinct source cells are disjoint.-/
private theorem atomicPairCell_disjoint_left {D E : FiniteWeightedDiagram}
    (j : E.supportLabels) {i k : D.supportLabels} (hik : i ≠ k) :
    Disjoint (atomicPairCell i j) (atomicPairCell k j) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzk
  have hi : z ∈ firstFiber {i.1} := hzi.1
  have hk : z ∈ firstFiber {k.1} := hzk.1
  rcases hi with ⟨x, hx, heqi⟩
  rcases hk with ⟨y, hy, heqk⟩
  have hxy : x = y := interiorIncl_injective (heqi.trans heqk.symm)
  have hik' : i.1 = k.1 := by simpa using hx.symm.trans (hxy.trans hy)
  exact hik (Subtype.ext hik')

private theorem atomicPairCell_row_measure_le {D E : FiniteWeightedDiagram}
    (π : Measure PlanSpace) (i : D.supportLabels) :
    (∑ j : E.supportLabels, π (atomicPairCell i j)) ≤
      π (firstFiber {i.1}) := by
  have hdisj : PairwiseDisjoint (Set.univ : Set E.supportLabels)
      (fun j => atomicPairCell i j) := by
    intro j _ k _ hjk
    exact atomicPairCell_disjoint_right i hjk
  have hsum := measure_biUnion_finset (μ := π) (s := Finset.univ) (by simpa using hdisj)
    (fun j _ => measurableSet_atomicPairCell i j)
  rw [← hsum]
  exact measure_mono (by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨j, _, hzj⟩
    exact hzj.1)

private theorem atomicPairCell_col_measure_le {D E : FiniteWeightedDiagram}
    (π : Measure PlanSpace) (j : E.supportLabels) :
    (∑ i : D.supportLabels, π (atomicPairCell i j)) ≤
      π (secondFiber {j.1}) := by
  have hdisj : PairwiseDisjoint (Set.univ : Set D.supportLabels)
      (fun i => atomicPairCell i j) := by
    intro i _ k _ hik
    exact atomicPairCell_disjoint_left j hik
  have hsum := measure_biUnion_finset (μ := π) (s := Finset.univ) (by simpa using hdisj)
    (fun i _ => measurableSet_atomicPairCell i j)
  rw [← hsum]
  exact measure_mono (by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨i, _, hzi⟩
    exact hzi.2)

/-- The interior–interior singleton masses of a Borel plan form a feasible native
weighted matrix. Finiteness comes from the two finite atomic marginals.-/
def extractedAtomicPlan {D E : FiniteWeightedDiagram} (π : Measure PlanSpace)
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E)) :
    FiniteWeightedBoundaryPlan D.weights E.weights := by
  letI : IsFiniteMeasure (atomicMeasure D) := atomicMeasure_isFinite D
  letI : IsFiniteMeasure (atomicMeasure E) := atomicMeasure_isFinite E
  letI : IsFiniteMeasure π := boundaryPlan_isFiniteMeasure hπ
  let m : D.supportLabels → E.supportLabels → ℝ :=
    fun i j => (π (atomicPairCell i j)).toReal
  have hfinite (s : Set PlanSpace) : π s ≠ ∞ :=
    ((measure_mono (subset_univ s)).trans_lt (measure_lt_top π Set.univ)).ne
  refine ⟨m, (fun i j => ENNReal.toReal_nonneg), ?_, ?_⟩
  · intro i
    have hrow := atomicPairCell_row_measure_le (D := D) (E := E) π i
    rw [hπ.first {i.1} (measurableSet_singleton i.1),
      atomicMeasure_singleton] at hrow
    have hreal := (ENNReal.toReal_le_toReal
      (by exact (ENNReal.sum_lt_top.mpr (fun j _ => (hfinite _).lt_top)).ne)
      ENNReal.coe_ne_top).2 hrow
    simpa only [m, FiniteWeightedDiagram.weights, ENNReal.toReal_sum
      (fun j _ => hfinite _), ENNReal.coe_toReal] using hreal
  · intro j
    have hcol := atomicPairCell_col_measure_le (D := D) (E := E) π j
    rw [hπ.second {j.1} (measurableSet_singleton j.1),
      atomicMeasure_singleton] at hcol
    have hreal := (ENNReal.toReal_le_toReal
      (by exact (ENNReal.sum_lt_top.mpr (fun i _ => (hfinite _).lt_top)).ne)
      ENNReal.coe_ne_top).2 hcol
    simpa only [m, FiniteWeightedDiagram.weights, ENNReal.toReal_sum
      (fun i _ => hfinite _), ENNReal.coe_toReal] using hreal

/-- A source atom paired with any (possibly non-nearest) diagonal endpoint.-/
def atomicDeleteCell {D : FiniteWeightedDiagram} (i : D.supportLabels) :
    Set PlanSpace := firstFiber {i.1} \ secondFiber Set.univ

/-- A target atom paired with any (possibly non-nearest) diagonal endpoint.-/
def atomicInsertCell {E : FiniteWeightedDiagram} (j : E.supportLabels) :
    Set PlanSpace := secondFiber {j.1} \ firstFiber Set.univ

theorem measurableSet_atomicDeleteCell {D : FiniteWeightedDiagram}
    (i : D.supportLabels) : MeasurableSet (atomicDeleteCell i) :=
  (measurableSet_firstFiber (measurableSet_singleton i.1)).diff
    (measurableSet_secondFiber MeasurableSet.univ)

theorem measurableSet_atomicInsertCell {E : FiniteWeightedDiagram}
    (j : E.supportLabels) : MeasurableSet (atomicInsertCell j) :=
  (measurableSet_secondFiber (measurableSet_singleton j.1)).diff
    (measurableSet_firstFiber MeasurableSet.univ)

private abbrev AtomicCellIndex (D E : FiniteWeightedDiagram) :=
  (D.supportLabels × E.supportLabels) ⊕ (D.supportLabels ⊕ E.supportLabels)

private def atomicCell {D E : FiniteWeightedDiagram} :
    AtomicCellIndex D E → Set PlanSpace
  | .inl (i, j) => atomicPairCell i j
  | .inr (.inl i) => atomicDeleteCell i
  | .inr (.inr j) => atomicInsertCell j

private def atomicCellCharge (p : ℝ) {D E : FiniteWeightedDiagram} :
    AtomicCellIndex D E → ℝ≥0∞
  | .inl (i, j) =>
      ENNReal.ofReal ((finitePairCost (D.coordinates i) (E.coordinates j)).toReal ^ p)
  | .inr (.inl i) =>
      ENNReal.ofReal ((diagonalCost (D.coordinates i)).toReal ^ p)
  | .inr (.inr j) =>
      ENNReal.ofReal ((diagonalCost (E.coordinates j)).toReal ^ p)

end TDA.Persistence.BoundaryTransport
