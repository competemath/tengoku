/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.MeasureTheory.Constructions.Pi
public import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.WithDensity
public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Dirichlet.Basic
public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Gamma.PDF

/-!
# The density of the Dirichlet distribution in a simplex chart

The Dirichlet law is carried by the standard simplex, which lies inside the affine hyperplane
`∑ i, x i = 1` of `EuclideanSpace ℝ ι`, so it has no density against the ambient volume.  This
file gives its density in the chart that drops one coordinate: after choosing `i₀ : ι`, a point of
the simplex is determined by its coordinates away from `i₀`, the coordinate at `i₀` being the
remaining mass `1 - ∑ j, x j`.

The Dirichlet law is defined by normalizing independent unit-rate Gamma coordinates by their
total, so the density comes from a change of variables that separates that total from the point of
the simplex it normalizes to.  Writing the Gamma coordinates as `(s, y)` with `s` the total and `y`
the chart coordinates, the change of variables has Jacobian `s ^ (card ι - 1)`, and the transported
Gamma product density factors as the chart density times a Gamma density of shape `∑ i, a i` in
`s`.  Integrating `s` out leaves the chart density.

## Main definitions

* `TauCeti.Probability.dirichletChart` reconstructs a point of `EuclideanSpace ℝ ι` from its
  coordinates away from `i₀`;
* `TauCeti.Probability.dirichletChartRegion` is the part of the chart mapping onto the strictly
  positive part of the simplex;
* `TauCeti.Probability.dirichletChartPDFReal` and `TauCeti.Probability.dirichletChartPDF` are the
  real- and `ℝ≥0∞`-valued densities in that chart, which describe the Dirichlet law at a positive
  concentration vector;
* `TauCeti.Probability.dirichletUnchart` and `TauCeti.Probability.dirichletChartCoords` are the
  two directions of the scaling change of variables, between
  `TauCeti.Probability.dirichletUnchartSource` and `TauCeti.Probability.dirichletUnchartTarget`.

## Main results

* `TauCeti.Probability.det_fderiv_dirichletUnchart` and
  `TauCeti.Probability.map_dirichletUnchart_withDensity` are the Jacobian of the scaling change of
  variables and the resulting identity of Lebesgue measures;
* `TauCeti.Probability.dirichletMeasure_eq_map_withDensity_dirichletChartPDF` presents the
  Dirichlet law as the image, under the chart, of Lebesgue measure on the remaining coordinates
  weighted by `TauCeti.Probability.dirichletChartPDF`;
* `TauCeti.Probability.lintegral_dirichletChartPDF_eq_one` records that this density has total
  mass one.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/
public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ : ι}

/-! ### The simplex chart -/

/-- Reconstruct a point of `EuclideanSpace ℝ ι` from its coordinates away from `i₀`, assigning the
remaining mass `1 - ∑ j, x j` to the coordinate `i₀`. -/
def dirichletChart (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) : EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm ((Equiv.funSplitAt i₀ ℝ).symm (1 - ∑ j, x j, x))

/-- The coordinate of a reconstructed point at the dropped index is the remaining mass. -/
@[simp]
theorem dirichletChart_apply_self (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) :
    dirichletChart i₀ x i₀ = 1 - ∑ j, x j := by
  simp [dirichletChart]

/-- The chart keeps the displayed coordinates. -/
@[simp]
theorem dirichletChart_apply_coe (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) (j : {i // i ≠ i₀}) :
    dirichletChart i₀ x j = x j := by
  simp [dirichletChart, j.2]

/-- The value of the chart at an index other than `i₀`, indexed by `ι` rather than by the
subtype. -/
@[simp]
theorem dirichletChart_apply_of_ne {i : ι} (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) (h : i ≠ i₀) :
    dirichletChart i₀ x i = x ⟨i, h⟩ :=
  dirichletChart_apply_coe i₀ x ⟨i, h⟩

/-- The chart is continuous. -/
@[fun_prop]
theorem continuous_dirichletChart : Continuous (dirichletChart i₀) := by
  refine (EuclideanSpace.equiv ι ℝ).symm.continuous.comp (continuous_pi fun i ↦ ?_)
  simp only [Equiv.funSplitAt_symm_apply]
  split_ifs with h
  · fun_prop
  · fun_prop

/-- The chart is measurable. -/
@[fun_prop]
theorem measurable_dirichletChart : Measurable (dirichletChart i₀) :=
  continuous_dirichletChart.measurable

/-- The coordinates of a reconstructed point sum to one. -/
@[simp]
theorem sum_dirichletChart (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) :
    ∑ i, dirichletChart i₀ x i = 1 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ dirichletChart i₀ x i) i₀]
  simp

/-- The chart is injective. -/
theorem dirichletChart_injective (i₀ : ι) :
    Function.Injective (dirichletChart i₀ (ι := ι)) := fun _ _ hxy ↦
  congrArg Prod.snd ((Equiv.funSplitAt i₀ ℝ).symm.injective
    ((EuclideanSpace.equiv ι ℝ).symm.injective hxy))

/-- The chart recovers a point of `EuclideanSpace ℝ ι` from its own coordinates away from `i₀`
exactly when the coordinates of that point sum to one: the image of the chart is the whole
hyperplane `∑ i, p i = 1`. -/
theorem dirichletChart_eq_self_iff (i₀ : ι) (p : EuclideanSpace ℝ ι) :
    dirichletChart i₀ (fun j : {i // i ≠ i₀} ↦ p j) = p ↔ ∑ i, p i = 1 := by
  have hsplit : ∑ i, p i = p i₀ + ∑ j : {i // i ≠ i₀}, p j :=
    Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ p i) i₀
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact sum_dirichletChart i₀ _
  · ext i
    by_cases hi : i = i₀
    · subst hi
      rw [dirichletChart_apply_self]
      linarith
    · rw [dirichletChart_apply_of_ne i₀ _ hi]

/-- The chart region: the coordinate vectors with positive coordinates of total less than one.
These are exactly the ones the chart sends to points of the standard simplex all of whose
coordinates are strictly positive, that is, to its relative interior inside the affine hyperplane
`∑ i, x i = 1`.  The simplex has empty interior in the ambient `EuclideanSpace ℝ ι`. -/
def dirichletChartRegion (i₀ : ι) : Set ({i // i ≠ i₀} → ℝ) :=
  {x | (∀ j, 0 < x j) ∧ ∑ j, x j < 1}

/-- Membership in the chart region, unfolded. -/
@[simp]
theorem mem_dirichletChartRegion_iff {x : {i // i ≠ i₀} → ℝ} :
    x ∈ dirichletChartRegion i₀ ↔ (∀ j, 0 < x j) ∧ ∑ j, x j < 1 := Iff.rfl

/-- The chart region is open. -/
theorem isOpen_dirichletChartRegion (i₀ : ι) : IsOpen (dirichletChartRegion i₀) := by
  have h₁ : IsOpen {x : {i // i ≠ i₀} → ℝ | ∀ j, 0 < x j} := by
    simpa only [Set.ofPred_forall] using
      isOpen_iInter_of_finite fun j ↦ isOpen_lt continuous_const (continuous_apply j)
  rw [dirichletChartRegion, Set.ofPred_and]
  exact h₁.inter (isOpen_lt (by fun_prop) continuous_const)

/-- The chart region is measurable. -/
theorem measurableSet_dirichletChartRegion (i₀ : ι) :
    MeasurableSet (dirichletChartRegion i₀) :=
  (isOpen_dirichletChartRegion i₀).measurableSet

/-- On the chart region every reconstructed coordinate is strictly positive. -/
theorem dirichletChart_pos {x : {i // i ≠ i₀} → ℝ} (hx : x ∈ dirichletChartRegion i₀) (i : ι) :
    0 < dirichletChart i₀ x i := by
  by_cases h : i = i₀
  · simpa [h] using sub_pos.mpr hx.2
  · simpa [dirichletChart_apply_of_ne i₀ x h] using hx.1 ⟨i, h⟩

/-- The chart carries the chart region onto the points of the standard simplex all of whose
coordinates are strictly positive. -/
theorem dirichletChart_image_region (i₀ : ι) :
    dirichletChart i₀ '' dirichletChartRegion i₀
      = {p : EuclideanSpace ℝ ι | (∀ i, 0 < p i) ∧ ∑ i, p i = 1} := by
  refine Set.Subset.antisymm ?_ fun p hp ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨dirichletChart_pos hx, sum_dirichletChart i₀ x⟩
  · have hsplit : ∑ i, p i = p i₀ + ∑ j : {i // i ≠ i₀}, p j :=
      Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ p i) i₀
    have hi₀ : 0 < p i₀ := hp.1 i₀
    have hsum : ∑ j : {i // i ≠ i₀}, p j < 1 := by
      have := hp.2
      linarith
    exact ⟨fun j : {i // i ≠ i₀} ↦ p j, ⟨fun j ↦ hp.1 j, hsum⟩,
      (dirichletChart_eq_self_iff i₀ p).2 hp.2⟩

/-! ### The chart density -/

open Classical in
/-- The real-valued density of the Dirichlet law with concentration vector `a` in the chart at
`i₀`, with respect to Lebesgue measure on the coordinates away from `i₀`.  It vanishes outside the
chart region.

The formula is defined for every `a`, but it describes `dirichletMeasure a` only for a positive
concentration vector: outside that range the Dirichlet measure is zero while this formula is
not. -/
def dirichletChartPDFReal (a : ι → ℝ) (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) : ℝ :=
  if x ∈ dirichletChartRegion i₀ then
    (Real.Gamma (∑ i, a i) / ∏ i, Real.Gamma (a i)) * (∏ j, x j ^ (a j - 1)) *
      (1 - ∑ j, x j) ^ (a i₀ - 1)
  else 0

/-- The `ℝ≥0∞`-valued density of the Dirichlet law in the chart at `i₀`.  As for
`TauCeti.Probability.dirichletChartPDFReal`, it describes the Dirichlet law at a positive
concentration vector. -/
def dirichletChartPDF (a : ι → ℝ) (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (dirichletChartPDFReal a i₀ x)

/-- The `ℝ≥0∞`-valued chart density is `ENNReal.ofReal` of the real-valued one. -/
theorem dirichletChartPDF_eq_ofReal (a : ι → ℝ) (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) :
    dirichletChartPDF a i₀ x = ENNReal.ofReal (dirichletChartPDFReal a i₀ x) := by
  rw [dirichletChartPDF]

/-- The value of the chart density on the chart region. -/
@[simp]
theorem dirichletChartPDFReal_of_mem (a : ι → ℝ) {x : ({i // i ≠ i₀}) → ℝ}
    (hx : x ∈ dirichletChartRegion i₀) :
    dirichletChartPDFReal a i₀ x =
      (Real.Gamma (∑ i, a i) / ∏ i, Real.Gamma (a i)) * (∏ j, x j ^ (a j - 1)) *
        (1 - ∑ j, x j) ^ (a i₀ - 1) :=
  ite_eq_left hx

/-- The chart density vanishes off the chart region. -/
@[simp]
theorem dirichletChartPDFReal_of_notMem (a : ι → ℝ) {x : ({i // i ≠ i₀}) → ℝ}
    (hx : x ∉ dirichletChartRegion i₀) :
    dirichletChartPDFReal a i₀ x = 0 :=
  ite_eq_right hx

/-- The `ℝ≥0∞`-valued chart density vanishes off the chart region. -/
@[simp]
theorem dirichletChartPDF_of_notMem (a : ι → ℝ) {x : ({i // i ≠ i₀}) → ℝ}
    (hx : x ∉ dirichletChartRegion i₀) :
    dirichletChartPDF a i₀ x = 0 := by
  rw [dirichletChartPDF_eq_ofReal, dirichletChartPDFReal_of_notMem a hx, ENNReal.ofReal_zero]

/-- The value of the `ℝ≥0∞`-valued chart density on the chart region. -/
@[simp]
theorem dirichletChartPDF_of_mem (a : ι → ℝ) {x : ({i // i ≠ i₀}) → ℝ}
    (hx : x ∈ dirichletChartRegion i₀) :
    dirichletChartPDF a i₀ x = ENNReal.ofReal
      ((Real.Gamma (∑ i, a i) / ∏ i, Real.Gamma (a i)) * (∏ j, x j ^ (a j - 1)) *
        (1 - ∑ j, x j) ^ (a i₀ - 1)) := by
  rw [dirichletChartPDF_eq_ofReal, dirichletChartPDFReal_of_mem a hx]

/-- The chart density is nonnegative at a positive concentration vector. -/
theorem dirichletChartPDFReal_nonneg {a : ι → ℝ} (ha : ∀ i, 0 < a i) (i₀ : ι)
    (x : {i // i ≠ i₀} → ℝ) :
    0 ≤ dirichletChartPDFReal a i₀ x := by
  rw [dirichletChartPDFReal]
  split_ifs with hx
  · have hΓ : 0 < Real.Gamma (∑ i, a i) :=
      Real.Gamma_pos_of_pos (Finset.sum_pos (fun i _ ↦ ha i) ⟨i₀, Finset.mem_univ i₀⟩)
    have hΓ' : 0 < ∏ i, Real.Gamma (a i) :=
      Finset.prod_pos fun i _ ↦ Real.Gamma_pos_of_pos (ha i)
    have h₁ : 0 ≤ ∏ j, x j ^ (a j - 1) :=
      Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx.1 j).le _
    have h₂ : 0 ≤ (1 - ∑ j, x j) ^ (a i₀ - 1) :=
      Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _
    positivity
  · exact le_rfl

/-- The chart density is measurable. -/
@[fun_prop]
theorem measurable_dirichletChartPDFReal (a : ι → ℝ) (i₀ : ι) :
    Measurable (dirichletChartPDFReal a i₀) := by
  classical
  refine Measurable.ite (measurableSet_dirichletChartRegion i₀) ?_ measurable_const
  refine ((measurable_const.mul ?_).mul ?_)
  · exact Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
  · exact (measurable_const.sub
      (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)).pow_const _

/-- The `ℝ≥0∞`-valued chart density is measurable. -/
@[fun_prop]
theorem measurable_dirichletChartPDF (a : ι → ℝ) (i₀ : ι) :
    Measurable (dirichletChartPDF a i₀) :=
  (measurable_dirichletChartPDFReal a i₀).ennreal_ofReal

/-! ### The scaling change of variables -/

/-- Reconstruct the raw coordinates from a total `z.1` and a point `z.2` of the chart: the
coordinate at `i₀` is `z.1 * (1 - ∑ j, z.2 j)` and the coordinate at `j` is `z.1 * z.2 j`. -/
def dirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) : ℝ × ({i // i ≠ i₀} → ℝ) :=
  (z.1 * (1 - ∑ j, z.2 j), fun j ↦ z.1 * z.2 j)

/-- The reconstructed coordinate at the dropped index `i₀`. -/
@[simp]
theorem dirichletUnchart_fst (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    (dirichletUnchart i₀ z).1 = z.1 * (1 - ∑ j, z.2 j) := by
  simp [dirichletUnchart]

/-- The reconstructed coordinate at an index other than `i₀`. -/
@[simp]
theorem dirichletUnchart_snd_apply (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ))
    (j : {i // i ≠ i₀}) : (dirichletUnchart i₀ z).2 j = z.1 * z.2 j := by
  simp [dirichletUnchart]

/-- Read off the total of the raw coordinates together with the chart coordinates they normalize
to, the coordinate at `i₀` being carried separately as `z.1`. -/
def dirichletChartCoords (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) : ℝ × ({i // i ≠ i₀} → ℝ) :=
  (z.1 + ∑ j, z.2 j, fun j ↦ z.2 j / (z.1 + ∑ j, z.2 j))

/-- The total of the raw coordinates. -/
@[simp]
theorem dirichletChartCoords_fst (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    (dirichletChartCoords i₀ z).1 = z.1 + ∑ j, z.2 j := by
  simp [dirichletChartCoords]

/-- The chart coordinate at `j`: the raw coordinate there divided by the total. -/
@[simp]
theorem dirichletChartCoords_snd_apply (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ))
    (j : {i // i ≠ i₀}) : (dirichletChartCoords i₀ z).2 j = z.2 j / (z.1 + ∑ j, z.2 j) := by
  simp [dirichletChartCoords]

/-- The source region of the scaling change of variables: a positive total together with a point
of the chart region. -/
def dirichletUnchartSource (i₀ : ι) : Set (ℝ × ({i // i ≠ i₀} → ℝ)) :=
  Ioi 0 ×ˢ dirichletChartRegion i₀

/-- Membership in the source region, unfolded. -/
@[simp]
theorem mem_dirichletUnchartSource_iff {z : ℝ × ({i // i ≠ i₀} → ℝ)} :
    z ∈ dirichletUnchartSource i₀ ↔ 0 < z.1 ∧ (∀ j, 0 < z.2 j) ∧ ∑ j, z.2 j < 1 := Iff.rfl

/-- The target region of the scaling change of variables: the open positive orthant. -/
def dirichletUnchartTarget (i₀ : ι) : Set (ℝ × ({i // i ≠ i₀} → ℝ)) :=
  Ioi 0 ×ˢ {y | ∀ j, 0 < y j}

omit [Fintype ι] [DecidableEq ι] in
/-- Membership in the target region, unfolded. -/
@[simp]
theorem mem_dirichletUnchartTarget_iff {z : ℝ × ({i // i ≠ i₀} → ℝ)} :
    z ∈ dirichletUnchartTarget i₀ ↔ 0 < z.1 ∧ ∀ j, 0 < z.2 j := Iff.rfl

/-- The scaling map is measurable. -/
@[fun_prop]
theorem measurable_dirichletUnchart (i₀ : ι) : Measurable (dirichletUnchart i₀) := by
  unfold dirichletUnchart
  fun_prop

/-- The source region is measurable. -/
theorem measurableSet_dirichletUnchartSource (i₀ : ι) :
    MeasurableSet (dirichletUnchartSource i₀) :=
  measurableSet_Ioi.prod (measurableSet_dirichletChartRegion i₀)

omit [Fintype ι] [DecidableEq ι] in
/-- The target region is measurable. -/
theorem measurableSet_dirichletUnchartTarget [Countable ι] (i₀ : ι) :
    MeasurableSet (dirichletUnchartTarget i₀) := by
  refine measurableSet_Ioi.prod ?_
  simpa only [Set.ofPred_forall] using
    MeasurableSet.iInter fun j ↦ measurableSet_lt measurable_const (measurable_pi_apply j)

/-- The scaling map sends the source region into the target region. -/
theorem dirichletUnchart_mem_target {i₀ : ι} {z : ℝ × ({i // i ≠ i₀} → ℝ)}
    (hz : z ∈ dirichletUnchartSource i₀) : dirichletUnchart i₀ z ∈ dirichletUnchartTarget i₀ := by
  obtain ⟨hs, hy⟩ := hz
  exact ⟨mul_pos hs (sub_pos.mpr hy.2), fun j ↦ mul_pos hs (hy.1 j)⟩

/-- The coordinate map sends the target region into the source region. -/
theorem dirichletChartCoords_mem_source {i₀ : ι} {z : ℝ × ({i // i ≠ i₀} → ℝ)}
    (hz : z ∈ dirichletUnchartTarget i₀) :
    dirichletChartCoords i₀ z ∈ dirichletUnchartSource i₀ := by
  obtain ⟨hu, hv⟩ := hz
  have hu' : 0 < z.1 := hu
  have hsum : 0 < z.1 + ∑ j, z.2 j :=
    add_pos_of_pos_of_nonneg hu' (Finset.sum_nonneg fun j _ ↦ (hv j).le)
  refine ⟨hsum, fun j ↦ div_pos (hv j) hsum, ?_⟩
  simp only [dirichletChartCoords_snd_apply, ← Finset.sum_div]
  rw [div_lt_one hsum]
  linarith

/-- The coordinate map inverts the scaling map on the source region. -/
theorem dirichletChartCoords_dirichletUnchart {i₀ : ι} {z : ℝ × ({i // i ≠ i₀} → ℝ)}
    (hz : z ∈ dirichletUnchartSource i₀) :
    dirichletChartCoords i₀ (dirichletUnchart i₀ z) = z := by
  obtain ⟨hs, hy⟩ := hz
  have hs' : 0 < z.1 := hs
  have hsum : z.1 * (1 - ∑ j, z.2 j) + ∑ j, z.1 * z.2 j = z.1 := by
    rw [← Finset.mul_sum]; ring
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simpa [dirichletChartCoords_fst] using hsum
  · simp only [dirichletChartCoords_snd_apply, dirichletUnchart_fst,
      dirichletUnchart_snd_apply, hsum]
    field_simp

/-- The scaling map inverts the coordinate map on the target region. -/
theorem dirichletUnchart_dirichletChartCoords {i₀ : ι} {z : ℝ × ({i // i ≠ i₀} → ℝ)}
    (hz : z ∈ dirichletUnchartTarget i₀) :
    dirichletUnchart i₀ (dirichletChartCoords i₀ z) = z := by
  obtain ⟨hu, hv⟩ := hz
  have hu' : 0 < z.1 := hu
  have hsum : 0 < z.1 + ∑ j, z.2 j :=
    add_pos_of_pos_of_nonneg hu' (Finset.sum_nonneg fun j _ ↦ (hv j).le)
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simp only [dirichletUnchart_fst, dirichletChartCoords_fst, dirichletChartCoords_snd_apply,
      ← Finset.sum_div]
    field_simp
    ring
  · simp only [dirichletUnchart_snd_apply, dirichletChartCoords_fst,
      dirichletChartCoords_snd_apply]
    rw [mul_comm, div_mul_cancel₀ _ hsum.ne']

/-- The scaling map is injective on the source region. -/
theorem dirichletUnchart_injOn (i₀ : ι) :
    Set.InjOn (dirichletUnchart i₀) (dirichletUnchartSource i₀) := fun z hz w hw h ↦ by
  rw [← dirichletChartCoords_dirichletUnchart hz, ← dirichletChartCoords_dirichletUnchart hw, h]

/-- The scaling map carries the source region onto the target region. -/
theorem dirichletUnchart_image_source (i₀ : ι) :
    dirichletUnchart i₀ '' dirichletUnchartSource i₀ = dirichletUnchartTarget i₀ := by
  refine Set.Subset.antisymm ?_ fun z hz ↦ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact dirichletUnchart_mem_target hz
  · exact ⟨dirichletChartCoords i₀ z, dirichletChartCoords_mem_source hz,
      dirichletUnchart_dirichletChartCoords hz⟩

/-- The derivative of `TauCeti.Probability.dirichletUnchart` at `z`. -/
def fderivDirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    (ℝ × ({i // i ≠ i₀} → ℝ)) →L[ℝ] ℝ × ({i // i ≠ i₀} → ℝ) :=
  (((1 - ∑ j, z.2 j) • ContinuousLinearMap.fst ℝ ℝ ({i // i ≠ i₀} → ℝ)) -
      z.1 • ((∑ j, ContinuousLinearMap.proj j) ∘L
        ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ({i // i ≠ i₀} → ℝ)).smulRight z.2 +
      z.1 • ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ))

/-- The value of the derivative of the scaling map. -/
@[simp]
theorem fderivDirichletUnchart_apply (i₀ : ι) (z w : ℝ × ({i // i ≠ i₀} → ℝ)) :
    fderivDirichletUnchart i₀ z w =
      (w.1 * (1 - ∑ j, z.2 j) - z.1 * ∑ j, w.2 j, fun j ↦ w.1 * z.2 j + z.1 * w.2 j) := by
  refine Prod.ext ?_ (funext fun j ↦ ?_) <;>
    simp [fderivDirichletUnchart, Finset.mul_sum, mul_comm]

/-- The stated continuous linear map is the derivative of the scaling map. -/
theorem hasFDerivAt_dirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    HasFDerivAt (dirichletUnchart i₀) (fderivDirichletUnchart i₀ z) z := by
  have hfst : HasFDerivAt (fun w : ℝ × ({i // i ≠ i₀} → ℝ) ↦ w.1)
      (ContinuousLinearMap.fst ℝ ℝ ({i // i ≠ i₀} → ℝ)) z := hasFDerivAt_fst
  have hsnd (j : {i // i ≠ i₀}) : HasFDerivAt (fun w : ℝ × ({i // i ≠ i₀} → ℝ) ↦ w.2 j)
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ))) z :=
    ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ))).hasFDerivAt
  have hsum : HasFDerivAt (fun w : ℝ × ({i // i ≠ i₀} → ℝ) ↦ 1 - ∑ j, w.2 j)
      (-((∑ j, ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ)))) z := by
    refine ((hasFDerivAt_const (1 : ℝ) z).fun_sub
      (HasFDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) ↦ hsnd j)).congr_fderiv ?_
    rw [zero_sub, ContinuousLinearMap.finsetSum_comp]
  unfold dirichletUnchart
  refine HasFDerivAt.prodMk ?_ ?_
  · refine (hfst.fun_mul hsum).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp only [sub_apply, add_apply, smul_apply, neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring
  · rw [hasFDerivAt_pi']
    intro j
    refine (hfst.fun_mul (hsnd j)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.proj_apply, add_apply, smul_apply, Pi.add_apply, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring

/-- `TauCeti.Probability.fderivDirichletUnchart` is the Fréchet derivative of the scaling map. -/
theorem fderiv_dirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    fderiv ℝ (dirichletUnchart i₀) z = fderivDirichletUnchart i₀ z :=
  (hasFDerivAt_dirichletUnchart i₀ z).fderiv

/-- The Jacobian determinant of the scaling change of variables is the total raised to the number
of coordinates other than `i₀`. -/
theorem det_fderiv_dirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    (fderiv ℝ (dirichletUnchart i₀) z).det = z.1 ^ Fintype.card {i // i ≠ i₀} := by
  classical
  rw [fderiv_dirichletUnchart]
  set M : Matrix (Unit ⊕ {i // i ≠ i₀}) (Unit ⊕ {i // i ≠ i₀}) ℝ :=
    Matrix.fromBlocks (Matrix.of fun _ _ ↦ 1 - ∑ j, z.2 j) (Matrix.of fun _ _ ↦ -z.1)
      (Matrix.of fun j _ ↦ z.2 j) (Matrix.diagonal fun _ ↦ z.1) with hM
  have htoMatrix : LinearMap.toMatrix
      ((Module.Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ ({i // i ≠ i₀})))
      ((Module.Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ ({i // i ≠ i₀})))
      (fderivDirichletUnchart i₀ z :
        (ℝ × ({i // i ≠ i₀} → ℝ)) →ₗ[ℝ] ℝ × ({i // i ≠ i₀} → ℝ)) = M := by
    ext (i | i) (j | j) <;>
      simp [hM, LinearMap.toMatrix_apply, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  have hdet : M.det = z.1 ^ Fintype.card {i // i ≠ i₀} := by
    set T : Matrix (Unit ⊕ {i // i ≠ i₀}) (Unit ⊕ {i // i ≠ i₀}) ℝ :=
      Matrix.fromBlocks 1 (Matrix.of fun _ _ ↦ (1 : ℝ)) 0 1 with hT
    have hTdet : T.det = 1 := by
      rw [hT, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
    have hTM : T * M =
        Matrix.fromBlocks 1 0 (Matrix.of fun j _ ↦ z.2 j) (Matrix.diagonal fun _ ↦ z.1) := by
      ext (i | i) (j | j) <;>
        simp [hT, hM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
          Matrix.diagonal_apply, eq_comm]
    have hsplit : M.det = (T * M).det := by rw [Matrix.det_mul, hTdet, one_mul]
    rw [hsplit, hTM, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    ((Module.Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ ({i // i ≠ i₀}))), htoMatrix, hdet]

/-- The Jacobian formula for the scaling change of variables, as an equality of restricted
Lebesgue measures. -/
theorem map_dirichletUnchart_withDensity (i₀ : ι) :
    Measure.map (dirichletUnchart i₀)
        ((volume.restrict (dirichletUnchartSource i₀)).withDensity
          fun z ↦ ENNReal.ofReal (z.1 ^ Fintype.card {i // i ≠ i₀})) =
      volume.restrict (dirichletUnchartTarget i₀) := by
  let _ : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ({i // i ≠ i₀} → ℝ))) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have heq : (fun z : ℝ × ({i // i ≠ i₀} → ℝ) ↦
        ENNReal.ofReal (z.1 ^ Fintype.card {i // i ≠ i₀}))
      =ᵐ[volume.restrict (dirichletUnchartSource i₀)]
      fun z ↦ ENNReal.ofReal |(fderivDirichletUnchart i₀ z).det| := by
    filter_upwards [ae_restrict_mem (measurableSet_dirichletUnchartSource i₀)] with z hz
    have hz1 : 0 < z.1 := hz.1
    rw [← fderiv_dirichletUnchart, det_fderiv_dirichletUnchart, abs_of_pos (pow_pos hz1 _)]
  rw [withDensity_congr_ae heq, ← dirichletUnchart_image_source]
  exact map_withDensity_abs_det_fderiv_eq_addHaar volume
    (measurableSet_dirichletUnchartSource i₀).nullMeasurableSet
    (fun z _ ↦ (hasFDerivAt_dirichletUnchart i₀ z).hasFDerivWithinAt)
    (dirichletUnchart_injOn i₀)

/-! ### The density computation -/

/-! ### The Dirichlet law in the chart -/

/-- The Gamma product density read in the split coordinates. -/
private def gammaSplitPDF (a : ι → ℝ) (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) : ℝ≥0∞ :=
  gammaPDF (a i₀) 1 z.1 * ∏ j : {i // i ≠ i₀}, gammaPDF (a j) 1 (z.2 j)

/-- The density of the total and the chart coordinates. -/
private def dirichletSourcePDF (a : ι → ℝ) (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) : ℝ≥0∞ :=
  gammaPDF (∑ i, a i) 1 z.1 * dirichletChartPDF a i₀ z.2

/-- The Gamma product, split off at `i₀`, is Lebesgue measure weighted by the product density. -/
private theorem prod_gammaMeasure_eq_withDensity (a : ι → ℝ) (i₀ : ι) :
    (gammaMeasure (a i₀) 1).prod (Measure.pi fun j : {i // i ≠ i₀} ↦ gammaMeasure (a j) 1)
      = volume.withDensity (gammaSplitPDF a i₀) := by
  rw [gammaMeasure, pi_gammaMeasure_eq_withDensity (fun j : {i // i ≠ i₀} ↦ a j) fun _ ↦ 1,
    prod_withDensity (f := gammaPDF (a i₀) 1)
      (g := fun x : {i // i ≠ i₀} → ℝ ↦ ∏ j : {i // i ≠ i₀}, gammaPDF (a j) 1 (x j))
      (measurable_gammaPDF (a i₀) 1)
      (Finset.measurable_prod _ fun (j : {i // i ≠ i₀}) _ ↦
        (measurable_gammaPDF (a j) 1).comp (measurable_pi_apply j)),
    ← Measure.volume_eq_prod]
  rfl

end Probability

end TauCeti
