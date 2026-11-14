import Tengoku.TdaLib.TDA.Persistence.BoundaryPlans
import Tengoku.TdaLib.TDA.Persistence.ReservoirMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From boundary plans to reservoir competitors

Collapse every boundary-plan endpoint, then add boundary–boundary mass to the
common capacity. Both reservoir marginals are obtained exactly, and powered
cost cannot increase. The construction applies to every admissible plan.
-/
set_option autoImplicit false
noncomputable section
namespace TDA.Persistence.BoundaryTransport
open Set MeasureTheory
open scoped ENNReal

/-- Collapse both closed half-plane coordinates of a genuine boundary-plan pair.-/
def collapsePlanPair (z : PlanSpace) : Space × Space :=
  (collapse z.1.1, collapse z.1.2)

/--
@isnad1 id=measurab.0h0v.s7.1fe29c81e179 from=translated src=- shape=1f28ec23 vocab=f6915585
-/
theorem measurable_collapsePlanPair : Measurable collapsePlanPair := by
  unfold collapsePlanPair
  exact (measurable_collapse.comp (by fun_prop)).prodMk
    (measurable_collapse.comp (by fun_prop))

/-- Add common boundary–boundary mass up to capacity `R`.-/
def collapsedAugmentation (π : Measure PlanSpace) (R : ℝ≥0∞) :
    Measure (Space × Space) :=
  π.map collapsePlanPair +
    (R - π Set.univ) • Measure.dirac (Space.boundary, Space.boundary)

/-- With sufficient capacity, the augmented plan has exactly mass `R`.
@isnad1 id=eq.1h2v.s9.0db84195d0e1 from=translated src=- shape=8fb6ec54 vocab=6bad3ae5
-/
theorem collapsedAugmentation_mass (π : Measure PlanSpace) (R : ℝ≥0∞)
    (hπR : π Set.univ ≤ R) :
    collapsedAugmentation π R Set.univ = R := by
  rw [collapsedAugmentation, Measure.add_apply,
    Measure.map_apply measurable_collapsePlanPair MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul]
  simp only [preimage_univ, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, mul_one]
  simpa only [add_comm] using (add_tsub_cancel_of_le hπR)

private theorem firstCollapse_preimage (s : Set Space)
    (hb : Space.boundary ∉ s) :
    (fun z : PlanSpace => collapse z.1.1) ⁻¹' s =
      firstFiber (Space.point ⁻¹' s) := by
  ext z
  change collapse z.1.1 ∈ s ↔ z.1.1 ∈ interiorIncl '' (Space.point ⁻¹' s)
  constructor
  · intro hz
    unfold collapse at hz
    split_ifs at hz with h
    · exact ⟨⟨z.1.1.1, h⟩, hz, rfl⟩
    · exact (hb hz).elim
  · rintro ⟨x, hx, heq⟩
    rw [← heq]
    change Space.point x ∈ s at hx
    simpa only [interiorIncl, collapse_interior] using hx

private theorem secondCollapse_preimage (s : Set Space)
    (hb : Space.boundary ∉ s) :
    (fun z : PlanSpace => collapse z.1.2) ⁻¹' s =
      secondFiber (Space.point ⁻¹' s) := by
  ext z
  change collapse z.1.2 ∈ s ↔ z.1.2 ∈ interiorIncl '' (Space.point ⁻¹' s)
  constructor
  · intro hz
    unfold collapse at hz
    split_ifs at hz with h
    · exact ⟨⟨z.1.2.1, h⟩, hz, rfl⟩
    · exact (hb hz).elim
  · rintro ⟨x, hx, heq⟩
    rw [← heq]
    change Space.point x ∈ s at hx
    simpa only [interiorIncl, collapse_interior] using hx

private theorem collapsedAugmentation_first_noboundary
    {π : Measure PlanSpace} {μ ν : Measure Interior}
    (hπ : IsBoundaryPlan π μ ν) (R : ℝ≥0∞)
    {s : Set Space} (hs : MeasurableSet s) (hb : Space.boundary ∉ s) :
    (collapsedAugmentation π R).map Prod.fst s = reservoirMeasure μ R s := by
  rw [Measure.map_apply (by fun_prop : Measurable (Prod.fst : Space × Space → Space)) hs,
    collapsedAugmentation, Measure.add_apply,
    Measure.map_apply measurable_collapsePlanPair
      ((by fun_prop : Measurable (Prod.fst : Space × Space → Space)) hs),
    Measure.smul_apply]
  have hpre : collapsePlanPair ⁻¹' (Prod.fst ⁻¹' s) =
      firstFiber (Space.point ⁻¹' s) := firstCollapse_preimage s hb
  rw [hpre, hπ.first _ (continuous_point.measurable hs)]
  simp [Measure.dirac_apply, hb, reservoirMeasure_apply_interior μ R hs hb]

private theorem collapsedAugmentation_second_noboundary
    {π : Measure PlanSpace} {μ ν : Measure Interior}
    (hπ : IsBoundaryPlan π μ ν) (R : ℝ≥0∞)
    {s : Set Space} (hs : MeasurableSet s) (hb : Space.boundary ∉ s) :
    (collapsedAugmentation π R).map Prod.snd s = reservoirMeasure ν R s := by
  rw [Measure.map_apply (by fun_prop : Measurable (Prod.snd : Space × Space → Space)) hs,
    collapsedAugmentation, Measure.add_apply,
    Measure.map_apply measurable_collapsePlanPair
      ((by fun_prop : Measurable (Prod.snd : Space × Space → Space)) hs),
    Measure.smul_apply]
  have hpre : collapsePlanPair ⁻¹' (Prod.snd ⁻¹' s) =
      secondFiber (Space.point ⁻¹' s) := secondCollapse_preimage s hb
  rw [hpre, hπ.second _ (continuous_point.measurable hs)]
  simp [Measure.dirac_apply, hb, reservoirMeasure_apply_interior ν R hs hb]

private theorem measure_eq_of_away_boundary_and_mass
    (A B : Measure Space) (hAfinite : A Set.univ < ∞)
    (hmass : A Set.univ = B Set.univ)
    (haway : ∀ s, MeasurableSet s → Space.boundary ∉ s → A s = B s) :
    A = B := by
  apply Measure.ext
  intro s hs
  by_cases hb : Space.boundary ∈ s
  · have hbc : Space.boundary ∉ sᶜ := by simpa using hb
    have hcomp : A sᶜ = B sᶜ := haway sᶜ hs.compl hbc
    have hAfinComp : A sᶜ ≠ ∞ :=
      ((measure_mono (subset_univ _)).trans_lt hAfinite).ne
    have hBfinite : B Set.univ < ∞ := by rw [← hmass]; exact hAfinite
    have hBfinComp : B sᶜ ≠ ∞ :=
      ((measure_mono (subset_univ _)).trans_lt hBfinite).ne
    have hAs : A s = A Set.univ - A sᶜ := by
      simpa only [compl_compl] using (measure_compl hs.compl hAfinComp)
    have hBs : B s = B Set.univ - B sᶜ := by
      simpa only [compl_compl] using (measure_compl hs.compl hBfinComp)
    rw [hAs, hBs, hmass, hcomp]
  · exact haway s hs hb

/-- The first projection of every collapsed, padded admissible plan is the
specified first reservoir measure.
@isnad1 id=eq.3h4v.s8.c38f3bc326ac from=translated src=- shape=fc5dad75 vocab=08029a6d
-/
theorem collapsedAugmentation_first_marginal
    {π : Measure PlanSpace} {μ ν : Measure Interior}
    (hπ : IsBoundaryPlan π μ ν) (R : ℝ≥0∞) (hR : R < ∞)
    (htotal : μ Set.univ + ν Set.univ ≤ R) :
    (collapsedAugmentation π R).map Prod.fst = reservoirMeasure μ R := by
  have hπR : π Set.univ ≤ R := (boundaryPlan_mass_le hπ).trans htotal
  have hμR : μ Set.univ ≤ R := le_self_add.trans htotal
  have hA : ((collapsedAugmentation π R).map Prod.fst) Set.univ = R := by
    rw [Measure.map_apply (by fun_prop : Measurable (Prod.fst : Space × Space → Space))
      MeasurableSet.univ, preimage_univ]
    exact collapsedAugmentation_mass π R hπR
  have hB : reservoirMeasure μ R Set.univ = R :=
    reservoirMeasure_mass μ R hμR
  apply measure_eq_of_away_boundary_and_mass _ _ (by rw [hA]; exact hR)
  · rw [hA, hB]
  · intro s hs hb
    exact collapsedAugmentation_first_noboundary hπ R hs hb

/-- The second projection is the specified second reservoir measure.
@isnad1 id=eq.3h4v.s8.8c72679d4be7 from=translated src=- shape=46563dad vocab=08029a6d
-/
theorem collapsedAugmentation_second_marginal
    {π : Measure PlanSpace} {μ ν : Measure Interior}
    (hπ : IsBoundaryPlan π μ ν) (R : ℝ≥0∞) (hR : R < ∞)
    (htotal : μ Set.univ + ν Set.univ ≤ R) :
    (collapsedAugmentation π R).map Prod.snd = reservoirMeasure ν R := by
  have hπR : π Set.univ ≤ R := (boundaryPlan_mass_le hπ).trans htotal
  have hνR : ν Set.univ ≤ R := by
    calc
      ν Set.univ ≤ ν Set.univ + μ Set.univ := le_self_add
      _ = μ Set.univ + ν Set.univ := add_comm _ _
      _ ≤ R := htotal
  have hA : ((collapsedAugmentation π R).map Prod.snd) Set.univ = R := by
    rw [Measure.map_apply (by fun_prop : Measurable (Prod.snd : Space × Space → Space))
      MeasurableSet.univ, preimage_univ]
    exact collapsedAugmentation_mass π R hπR
  have hB : reservoirMeasure ν R Set.univ = R :=
    reservoirMeasure_mass ν R hνR
  apply measure_eq_of_away_boundary_and_mass _ _ (by rw [hA]; exact hR)
  · rw [hA, hB]
  · intro s hs hb
    exact collapsedAugmentation_second_noboundary hπ R hs hb

/-- Pairwise collapsed distance never exceeds the original maximum-coordinate distance.
@isnad1 id=le.0h1v.s9.ebcb421ac772 from=translated src=- shape=887732fc vocab=b58c20b6
-/
theorem collapsePlanPair_dist_le (z : PlanSpace) :
    dist (collapse z.1.1) (collapse z.1.2) ≤ dist z.1.1 z.1.2 := by
  have h := lipschitz_collapse.dist_le_mul z.1.1 z.1.2
  simpa using h

/-- Powered cost decreases pointwise on collapse when `p` is nonnegative.
@isnad1 id=le.1h2v.s8.c3bffa9de27d from=translated src=- shape=930f663a vocab=b03dfe55
-/
theorem collapsePlanPair_powerCost_le (p : ℝ) (hp : 0 ≤ p) (z : PlanSpace) :
    ENNReal.ofReal ((dist (collapse z.1.1) (collapse z.1.2)) ^ p) ≤
      planPowerCost p z := by
  unfold planPowerCost
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow dist_nonneg (collapsePlanPair_dist_le z) hp)

/-- Powered metric cost on collapsed pairs.-/
def collapsedPowerCost (p : ℝ) (z : Space × Space) : ℝ≥0∞ :=
  ENNReal.ofReal ((dist z.1 z.2) ^ p)

/--
@isnad1 id=measurab.0h1v.s3.3ba7ae657080 from=translated src=- shape=360773cc vocab=c9563cdf
-/
theorem measurable_collapsedPowerCost (p : ℝ) : Measurable (collapsedPowerCost p) := by
  unfold collapsedPowerCost
  fun_prop

/-- Collapse plus boundary–boundary padding never raises powered cost, even for an
original competitor of infinite cost.
@isnad1 id=le.1h3v.s8.04306cdc0722 from=translated src=- shape=ea9287d9 vocab=66e3e524
-/
theorem collapsedAugmentation_cost_le (π : Measure PlanSpace) (R : ℝ≥0∞)
    (p : ℝ) (hp : 0 < p) :
    (∫⁻ z, collapsedPowerCost p z ∂collapsedAugmentation π R) ≤
      ∫⁻ z, planPowerCost p z ∂π := by
  rw [collapsedAugmentation, lintegral_add_measure, lintegral_smul_measure,
    lintegral_map (measurable_collapsedPowerCost p) measurable_collapsePlanPair]
  have hb : (∫⁻ z, collapsedPowerCost p z ∂Measure.dirac
      (Space.boundary, Space.boundary)) = 0 := by
    simp [collapsedPowerCost, Real.zero_rpow hp.ne']
  rw [hb]
  simp only [smul_eq_mul, mul_zero, add_zero]
  exact lintegral_mono fun z => collapsePlanPair_powerCost_le p hp.le z

/-- Forward boundary-to-reservoir comparison for every admissible Borel plan,
including those with infinite powered cost. The two conclusions are literal
pushforward marginal equalities on the collapsed metric space.
@isnad1 id=and.4h5v.s9.b162a1dd83da from=translated src=- shape=b44bd575 vocab=18a78f2c
-/
theorem collapsedAugmentation_forward
    {π : Measure PlanSpace} {μ ν : Measure Interior}
    (hπ : IsBoundaryPlan π μ ν) (R : ℝ≥0∞) (hR : R < ∞)
    (htotal : μ Set.univ + ν Set.univ ≤ R)
    (p : ℝ) (hp : 1 ≤ p) :
    (collapsedAugmentation π R).map Prod.fst = reservoirMeasure μ R ∧
      (collapsedAugmentation π R).map Prod.snd = reservoirMeasure ν R ∧
      (∫⁻ z, collapsedPowerCost p z ∂collapsedAugmentation π R) ≤
        ∫⁻ z, planPowerCost p z ∂π :=
  ⟨collapsedAugmentation_first_marginal hπ R hR htotal,
    collapsedAugmentation_second_marginal hπ R hR htotal,
    collapsedAugmentation_cost_le π R p (lt_of_lt_of_le zero_lt_one hp)⟩

end TDA.Persistence.BoundaryTransport
