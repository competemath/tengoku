import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportGeometry
import Tengoku.Seed.MeasureTheory.Measure.FiniteMeasure
import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite boundary plans

Plans on pairs of closed birth–death coordinates exclude diagonal–diagonal pairs.
Only their interior marginals are prescribed. Every admissible plan has mass at
most the sum of the input masses. Sending both inputs to their nearest diagonal
points gives an explicit finite-cost competitor when the diagonal persistence
moments are finite.
-/

set_option autoImplicit false

noncomputable section
namespace TDA.Persistence.BoundaryTransport
open Set MeasureTheory
open scoped ENNReal

/-- The canonical inclusion of strict bars in the closed half-plane.-/
def interiorIncl (x : Interior) : ClosedHalfPlane := ⟨x.1, x.2.le⟩

/-- The closest diagonal point in the maximum-coordinate norm.-/
def diagonalProjection (x : Interior) : ClosedHalfPlane :=
  ⟨((x.1.1 + x.1.2) / 2, (x.1.1 + x.1.2) / 2), le_rfl⟩

/-- Ordered pairs of closed half-plane points with at least one interior endpoint.-/
abbrev PlanSpace := {z : ClosedHalfPlane × ClosedHalfPlane //
  z.1.1.1 < z.1.1.2 ∨ z.2.1.1 < z.2.1.2}

/-- In the closed half-plane, the plan carrier is precisely the complement of
diagonal–diagonal pairs.
@isnad1 id=iff.0h1v.s8.4590d482d5ee from=translated src=- shape=ba5ca204 vocab=d63231f8
-/
theorem planSpace_iff_not_both_diagonal (z : ClosedHalfPlane × ClosedHalfPlane) :
    z ∈ Set.range (Subtype.val : PlanSpace → ClosedHalfPlane × ClosedHalfPlane) ↔
      ¬ (z.1.1.1 = z.1.1.2 ∧ z.2.1.1 = z.2.1.2) := by
  constructor
  · rintro ⟨e, rfl⟩ ⟨h₁, h₂⟩
    rcases e.2 with h | h
    · exact (ne_of_lt h) h₁
    · exact (ne_of_lt h) h₂
  · intro h
    by_cases h₁ : z.1.1.1 < z.1.1.2
    · exact ⟨⟨z, Or.inl h₁⟩, rfl⟩
    · have heq₁ : z.1.1.1 = z.1.1.2 :=
        le_antisymm z.1.2 (le_of_not_gt h₁)
      have h₂ : z.2.1.1 < z.2.1.2 := by
        by_contra hn
        exact h ⟨heq₁, le_antisymm z.2.2 (le_of_not_gt hn)⟩
      exact ⟨⟨z, Or.inr h₂⟩, rfl⟩

/-- The bars with an interior first endpoint lying in `s`.-/
def firstFiber (s : Set Interior) : Set PlanSpace :=
  {z | z.1.1 ∈ interiorIncl '' s}

/-- The bars with an interior second endpoint lying in `s`.-/
def secondFiber (s : Set Interior) : Set PlanSpace :=
  {z | z.1.2 ∈ interiorIncl '' s}

/-- A boundary plan has the specified two interior marginals; boundary marginals are free.-/
structure IsBoundaryPlan (π : Measure PlanSpace) (μ ν : Measure Interior) : Prop where
  first : ∀ s, MeasurableSet s → π (firstFiber s) = μ s
  second : ∀ s, MeasurableSet s → π (secondFiber s) = ν s

private theorem planSpace_cover :
    (Set.univ : Set PlanSpace) = firstFiber Set.univ ∪ secondFiber Set.univ := by
  ext z
  constructor
  · intro _
    rcases z.2 with h | h
    · left
      exact ⟨⟨z.1.1.1, h⟩, Set.mem_univ _, Subtype.ext rfl⟩
    · right
      exact ⟨⟨z.1.2.1, h⟩, Set.mem_univ _, Subtype.ext rfl⟩
  · intro _
    trivial

/-- Every admissible boundary plan has total mass at most the two input masses.
@isnad1 id=le.1h3v.s9.c2a31b4e371d from=translated src=- shape=7a5df092 vocab=ca20e6cf
-/
theorem boundaryPlan_mass_le {π : Measure PlanSpace} {μ ν : Measure Interior}
    (hπ : IsBoundaryPlan π μ ν) : π Set.univ ≤ μ Set.univ + ν Set.univ := by
  rw [planSpace_cover]
  exact (measure_union_le _ _).trans_eq
    (congrArg₂ (· + ·) (hπ.first _ MeasurableSet.univ)
      (hπ.second _ MeasurableSet.univ))

/-- Finite input masses force every admissible boundary plan to be finite.
@isnad1 id=lt.1h3v.s9.496b5897f02b from=translated src=- shape=c6068e82 vocab=0f257bbc
-/
theorem boundaryPlan_mass_lt_top {π : Measure PlanSpace} {μ ν : Measure Interior}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hπ : IsBoundaryPlan π μ ν) :
    π Set.univ < ∞ :=
  (boundaryPlan_mass_le hπ).trans_lt
    (ENNReal.add_lt_top.mpr ⟨measure_lt_top μ _, measure_lt_top ν _⟩)

/--
@isnad1 id=isfinite.1h3v.s8.7233f6daf7a1 from=translated src=- shape=75d9308c vocab=7876c22f
-/
theorem boundaryPlan_isFiniteMeasure {π : Measure PlanSpace} {μ ν : Measure Interior}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hπ : IsBoundaryPlan π μ ν) :
    IsFiniteMeasure π :=
  ⟨boundaryPlan_mass_lt_top hπ⟩

/-- A source bar is sent to its closest diagonal point.-/
def deleteLeg (x : Interior) : PlanSpace :=
  ⟨(interiorIncl x, diagonalProjection x), Or.inl x.2⟩

/-- A target bar is born at its closest diagonal point.-/
def insertLeg (x : Interior) : PlanSpace :=
  ⟨(diagonalProjection x, interiorIncl x), Or.inr x.2⟩

/--
@isnad1 id=continuo.0h0v.s6.dd381697f2e9 from=translated src=- shape=54c8eceb vocab=85120eb8
-/
theorem continuous_interiorIncl : Continuous interiorIncl := by
  unfold interiorIncl
  fun_prop

private instance : PolishSpace Interior := by
  have h : IsOpen {x : ℝ × ℝ | x.1 < x.2} :=
    isOpen_lt continuous_fst continuous_snd
  exact h.polishSpace

/--
@isnad1 id=injectiv.0h0v.s2.f36d7a1ac369 from=translated src=- shape=54c8eceb vocab=7aacfbe2
-/
theorem interiorIncl_injective : Function.Injective interiorIncl := by
  intro x y h
  have h' : x.1 = y.1 := by
    simpa only [interiorIncl] using congrArg Subtype.val h
  exact Subtype.ext h'

/--
@isnad1 id=measurab.0h0v.s5.4df498c40d16 from=translated src=- shape=54c8eceb vocab=5e43f171
-/
theorem measurableEmbedding_interiorIncl : MeasurableEmbedding interiorIncl :=
  continuous_interiorIncl.measurableEmbedding interiorIncl_injective

private theorem continuous_diagonalProjection : Continuous diagonalProjection := by
  unfold diagonalProjection
  fun_prop

/--
@isnad1 id=measurab.0h0v.s7.fdd4d2db857a from=translated src=- shape=54c8eceb vocab=8e91b554
-/
theorem measurable_deleteLeg : Measurable deleteLeg := by
  apply Continuous.measurable
  unfold deleteLeg
  exact (continuous_interiorIncl.prodMk continuous_diagonalProjection).subtype_mk _

/--
@isnad1 id=measurab.0h0v.s7.7d54a6dd1919 from=translated src=- shape=54c8eceb vocab=03a356ae
-/
theorem measurable_insertLeg : Measurable insertLeg := by
  apply Continuous.measurable
  unfold insertLeg
  exact (continuous_diagonalProjection.prodMk continuous_interiorIncl).subtype_mk _

/--
@isnad1 id=measurab.1h1v.s7.c7e505afe934 from=translated src=- shape=f82cf813 vocab=792680b8
-/
theorem measurableSet_firstFiber {s : Set Interior} (hs : MeasurableSet s) :
    MeasurableSet (firstFiber s) := by
  exact (measurableEmbedding_interiorIncl.measurableSet_image.mpr hs).preimage
    (by fun_prop : Measurable (fun z : PlanSpace => z.1.1))

/--
@isnad1 id=measurab.1h1v.s7.e34df029d857 from=translated src=- shape=f82cf813 vocab=a842ebce
-/
theorem measurableSet_secondFiber {s : Set Interior} (hs : MeasurableSet s) :
    MeasurableSet (secondFiber s) := by
  exact (measurableEmbedding_interiorIncl.measurableSet_image.mpr hs).preimage
    (by fun_prop : Measurable (fun z : PlanSpace => z.1.2))

/-- Explicit unmatched deletion and insertion measure.-/
def diagonalBoundaryPlan (μ ν : Measure Interior) : Measure PlanSpace :=
  μ.map deleteLeg + ν.map insertLeg

/-- The explicit nearest-diagonal plan has the required marginals.
@isnad1 id=isbounda.0h2v.s5.1c3a810f9027 from=translated src=- shape=4c3043c8 vocab=3cad9f47
-/
theorem diagonalBoundaryPlan_admissible (μ ν : Measure Interior) :
    IsBoundaryPlan (diagonalBoundaryPlan μ ν) μ ν := by
  have hfirstDelete (s : Set Interior) : deleteLeg ⁻¹' firstFiber s = s := by
    ext x
    change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (interiorIncl_injective hxy).symm ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hfirstInsert (s : Set Interior) : insertLeg ⁻¹' firstFiber s = ∅ := by
    ext x
    change diagonalProjection x ∈ interiorIncl '' s ↔ False
    constructor
    · rintro ⟨y, _, heq⟩
      have h : (diagonalProjection x).1.1 < (diagonalProjection x).1.2 := by
        rw [← heq]
        exact y.2
      simp [diagonalProjection] at h
    · intro h
      exact False.elim h
  have hsecondDelete (s : Set Interior) : deleteLeg ⁻¹' secondFiber s = ∅ := by
    ext x
    change diagonalProjection x ∈ interiorIncl '' s ↔ False
    constructor
    · rintro ⟨y, _, heq⟩
      have h : (diagonalProjection x).1.1 < (diagonalProjection x).1.2 := by
        rw [← heq]
        exact y.2
      simp [diagonalProjection] at h
    · intro h
      exact False.elim h
  have hsecondInsert (s : Set Interior) : insertLeg ⁻¹' secondFiber s = s := by
    ext x
    change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (interiorIncl_injective hxy).symm ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  constructor
  · intro s hs
    rw [diagonalBoundaryPlan, Measure.add_apply,
      Measure.map_apply measurable_deleteLeg (measurableSet_firstFiber hs),
      Measure.map_apply measurable_insertLeg (measurableSet_firstFiber hs)]
    rw [hfirstDelete, hfirstInsert]
    simp
  · intro s hs
    rw [diagonalBoundaryPlan, Measure.add_apply,
      Measure.map_apply measurable_deleteLeg (measurableSet_secondFiber hs),
      Measure.map_apply measurable_insertLeg (measurableSet_secondFiber hs)]
    rw [hsecondDelete, hsecondInsert]
    simp

/-- Its mass is exactly the sum of input masses, including zero and unequal masses.
@isnad1 id=eq.0h2v.s9.f940b7aa386a from=translated src=- shape=8b5b01ae vocab=df898fa7
-/
theorem diagonalBoundaryPlan_mass (μ ν : Measure Interior) :
    diagonalBoundaryPlan μ ν Set.univ = μ Set.univ + ν Set.univ := by
  rw [diagonalBoundaryPlan, Measure.add_apply,
    Measure.map_apply measurable_deleteLeg MeasurableSet.univ,
    Measure.map_apply measurable_insertLeg MeasurableSet.univ]
  simp

/-- Each deletion leg realizes the native diagonal cost.
@isnad1 id=eq.0h1v.s5.68cc55413876 from=translated src=- shape=ec30d5c2 vocab=1538ea08
-/
theorem deleteLeg_distance (x : Interior) :
    dist (interiorIncl x) (diagonalProjection x) = depth x := by
  rw [depth_eq]
  change dist x.1 ((x.1.1 + x.1.2) / 2, (x.1.1 + x.1.2) / 2) =
    (x.1.2 - x.1.1) / 2
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  rw [← diagonalCost_midpoint x.1.1 x.1.2]
  rw [abs_of_pos (sub_pos.mpr x.2)]

/--
@isnad1 id=eq.0h1v.s5.e8b2e22a4c2d from=translated src=- shape=ec30d5c2 vocab=1538ea08
-/
theorem insertLeg_distance (x : Interior) :
    dist (diagonalProjection x) (interiorIncl x) = depth x := by
  rw [dist_comm]
  exact deleteLeg_distance x

/-- Powered maximum-coordinate transport cost on the genuine boundary-plan space.-/
def planPowerCost (p : ℝ) (z : PlanSpace) : ℝ≥0∞ :=
  ENNReal.ofReal ((dist z.1.1 z.1.2) ^ p)

/--
@isnad1 id=measurab.0h1v.s7.0c3ed06a9725 from=translated src=- shape=7000f90d vocab=777ab7db
-/
theorem measurable_planPowerCost (p : ℝ) : Measurable (planPowerCost p) := by
  unfold planPowerCost
  fun_prop

/-- The explicit plan has exactly the two diagonal persistence moments as cost.
@isnad1 id=eq.0h3v.s8.1e09bb385896 from=translated src=- shape=d6ab10ae vocab=4504a6eb
-/
theorem diagonalBoundaryPlan_cost (p : ℝ) (μ ν : Measure Interior) :
    ∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ ν =
      (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) +
      (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) := by
  rw [diagonalBoundaryPlan, lintegral_add_measure,
    lintegral_map (measurable_planPowerCost p) measurable_deleteLeg,
    lintegral_map (measurable_planPowerCost p) measurable_insertLeg]
  simp only [planPowerCost, deleteLeg, insertLeg, deleteLeg_distance, insertLeg_distance]

/-- Finite p-persistence on both inputs gives one finite-cost admissible plan.
@isnad1 id=lt.2h3v.s8.43e106bbb7a3 from=translated src=- shape=161b2533 vocab=042e2e79
-/
theorem diagonalBoundaryPlan_cost_lt_top (p : ℝ) (μ ν : Measure Interior)
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞) :
    (∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ ν) < ∞ := by
  rw [diagonalBoundaryPlan_cost]
  exact ENNReal.add_lt_top.mpr ⟨hμ, hν⟩

/-- The finite-persistence hypotheses provide a real admissible finite-cost competitor.
@isnad1 id=ex.2h3v.s9.a58af97c3526 from=translated src=- shape=65b9cb0f vocab=24c3a981
-/
theorem exists_finite_cost_boundaryPlan (p : ℝ) (μ ν : Measure Interior)
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞) :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π μ ν ∧
      (∫⁻ z, planPowerCost p z ∂π) < ∞ :=
  ⟨diagonalBoundaryPlan μ ν, diagonalBoundaryPlan_admissible μ ν,
    diagonalBoundaryPlan_cost_lt_top p μ ν hμ hν⟩

/-- Powered boundary transport value over all admissible Borel plans.-/
def boundaryTransportPowerValue (p : ℝ) (μ ν : Measure Interior) : ℝ≥0∞ :=
  ⨅ (π : Measure PlanSpace) (_ : IsBoundaryPlan π μ ν),
    ∫⁻ z, planPowerCost p z ∂π

/--
@isnad1 id=le.0h3v.s7.40168e3706df from=translated src=- shape=36e676e7 vocab=0000eb6d
-/
theorem boundaryTransportPowerValue_le_diagonalPlan (p : ℝ) (μ ν : Measure Interior) :
    boundaryTransportPowerValue p μ ν ≤
      ∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ ν := by
  exact (iInf_le (fun π : Measure PlanSpace =>
    ⨅ (_ : IsBoundaryPlan π μ ν), ∫⁻ z, planPowerCost p z ∂π)
    (diagonalBoundaryPlan μ ν)).trans
      (iInf_le (fun _ : IsBoundaryPlan (diagonalBoundaryPlan μ ν) μ ν =>
        ∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ ν)
        (diagonalBoundaryPlan_admissible μ ν))

/--
@isnad1 id=lt.2h3v.s7.b9dbd2899576 from=translated src=- shape=54abdec8 vocab=9b431f1d
-/
theorem boundaryTransportPowerValue_lt_top (p : ℝ) (μ ν : Measure Interior)
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞) :
    boundaryTransportPowerValue p μ ν < ∞ :=
  (boundaryTransportPowerValue_le_diagonalPlan p μ ν).trans_lt
    (diagonalBoundaryPlan_cost_lt_top p μ ν hμ hν)

end TDA.Persistence.BoundaryTransport
