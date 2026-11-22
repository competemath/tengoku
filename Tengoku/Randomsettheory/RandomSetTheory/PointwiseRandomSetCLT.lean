/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.DirectedHausdorff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pointwise random-set CLT from a functional support-process limit

This file packages the three continuous-mapping conclusions appearing in the
pointwise random-set CLT: symmetric Hausdorff distance and the two orientations
of directed Hausdorff distance.  All three are derived from one weak limit of
the complete support-difference process on the closed unit ball.

The substantive tightness or Donsker theorem producing that process limit is
deliberately kept as an explicit premise.  In particular, this module does not
claim that a second-moment assumption alone has already supplied the functional
weak convergence.
-/

open Filter MeasureTheory Metric ProbabilityTheory Set Topology
open scoped InnerProductSpace ProbabilityTheory

noncomputable section

namespace RandomSetTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The zero direction, regarded as a point of the closed unit ball.-/
def closedUnitBallZero : Metric.closedBall (0 : E) 1 := ⟨0, by simp⟩

/-- The canonical inclusion of the unit sphere into the closed unit ball.-/
def unitSphereInClosedUnitBall :
    C(Metric.sphere (0 : E) 1, Metric.closedBall (0 : E) 1) where
  toFun u := ⟨u, Metric.sphere_subset_closedBall u.property⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.0h2v.s9.09e230eb8566 from=translated src=- shape=11f3503e vocab=fb6a8b78
-/
@[simp]
theorem coe_unitSphereInClosedUnitBall
    (u : Metric.sphere (0 : E) 1) :
    ((unitSphereInClosedUnitBall (E := E) u :
      Metric.closedBall (0 : E) 1) : E) = u := rfl

/-- Positive homogeneity restricted to pairs of points that both belong to
the closed unit ball.  This formulation avoids making the proof of membership
of a scaled point part of the hypothesis.-/
def PositivelyHomogeneousOnClosedUnitBall
    (f : C(Metric.closedBall (0 : E) 1, ℝ)) : Prop :=
  ∀ (x y : Metric.closedBall (0 : E) 1) (r : ℝ), 0 ≤ r →
    (y : E) = r • (x : E) → f y = r * f x

/-- Absolute value of a continuous path, restricted to the unit sphere.-/
def unitSphereAbsContinuousMap
    (f : C(Metric.closedBall (0 : E) 1, ℝ)) :
    C(Metric.sphere (0 : E) 1, ℝ) where
  toFun u := |f (unitSphereInClosedUnitBall (E := E) u)|
  continuous_toFun :=
    (f.continuous.comp (unitSphereInClosedUnitBall (E := E)).continuous).abs

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.0h3v.s10.1a1066f1ba9e from=translated src=- shape=bc0d8a12 vocab=75806eb3
-/
@[simp]
theorem unitSphereAbsContinuousMap_apply
    (f : C(Metric.closedBall (0 : E) 1, ℝ))
    (u : Metric.sphere (0 : E) 1) :
    unitSphereAbsContinuousMap f u =
      |f (unitSphereInClosedUnitBall (E := E) u)| := rfl

/-- Positive part of a continuous path, restricted to the unit sphere.-/
def unitSpherePositivePartContinuousMap
    (f : C(Metric.closedBall (0 : E) 1, ℝ)) :
    C(Metric.sphere (0 : E) 1, ℝ) where
  toFun u := max (f (unitSphereInClosedUnitBall (E := E) u)) 0
  continuous_toFun :=
    (f.continuous.comp (unitSphereInClosedUnitBall (E := E)).continuous).max
      continuous_const

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.0h3v.s10.154562b1c20a from=translated src=- shape=53248d60 vocab=8d612804
-/
@[simp]
theorem unitSpherePositivePartContinuousMap_apply
    (f : C(Metric.closedBall (0 : E) 1, ℝ))
    (u : Metric.sphere (0 : E) 1) :
    unitSpherePositivePartContinuousMap f u =
      max (f (unitSphereInClosedUnitBall (E := E) u)) 0 := rfl

/-- Supremum of the absolute value of a path over the unit sphere.-/
def unitSphereSupAbs (f : C(Metric.closedBall (0 : E) 1, ℝ)) : ℝ :=
  continuousSup (unitSphereAbsContinuousMap f)

/-- Supremum of the positive part of a path over the unit sphere.-/
def unitSphereSupPositivePart
    (f : C(Metric.closedBall (0 : E) 1, ℝ)) : ℝ :=
  continuousSup (unitSpherePositivePartContinuousMap f)

/-- Supremum over the unit sphere of the positive part of the negative path.-/
def unitSphereSupNegativePart
    (f : C(Metric.closedBall (0 : E) 1, ℝ)) : ℝ :=
  unitSphereSupPositivePart (-f)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `unitSphereSupAbs` is literally the supremum of `|f u|` over unit
directions.
@isnad1 id=eq.0h2v.s9.ccd1052a7273 from=translated src=- shape=6ca7d52a vocab=1fba875a
-/
theorem unitSphereSupAbs_eq_sSup_range
    (f : C(Metric.closedBall (0 : E) 1, ℝ)) :
    unitSphereSupAbs f = sSup (Set.range fun u : Metric.sphere (0 : E) 1 ↦
      |f (unitSphereInClosedUnitBall (E := E) u)|) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `unitSphereSupPositivePart` is literally the supremum of `(f u)₊` over
unit directions, with the positive part written as `max (f u) 0`.
@isnad1 id=eq.0h2v.s9.64a9738f5faf from=translated src=- shape=c363b63c vocab=bd61f125
-/
theorem unitSphereSupPositivePart_eq_sSup_range
    (f : C(Metric.closedBall (0 : E) 1, ℝ)) :
    unitSphereSupPositivePart f =
      sSup (Set.range fun u : Metric.sphere (0 : E) 1 ↦
        max (f (unitSphereInClosedUnitBall (E := E) u)) 0) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `unitSphereSupNegativePart` is literally the supremum of `(-f u)₊` over
unit directions.
@isnad1 id=eq.0h2v.s9.ee0fc6fc78ef from=translated src=- shape=8c84ef84 vocab=1016a397
-/
theorem unitSphereSupNegativePart_eq_sSup_range
    (f : C(Metric.closedBall (0 : E) 1, ℝ)) :
    unitSphereSupNegativePart f =
      sSup (Set.range fun u : Metric.sphere (0 : E) 1 ↦
        max (-f (unitSphereInClosedUnitBall (E := E) u)) 0) := rfl

private theorem exists_continuousSup_eq_and_ge
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [Nonempty T]
    (f : C(T, ℝ)) :
    ∃ x : T, continuousSup f = f x ∧ ∀ y : T, f y ≤ f x := by
  obtain ⟨x, -, hx, hmax⟩ :=
    isCompact_univ.exists_sSup_image_eq_and_ge
      (Set.univ_nonempty : (Set.univ : Set T).Nonempty)
      f.continuous.continuousOn
  refine ⟨x, ?_, fun y ↦ hmax y (Set.mem_univ y)⟩
  simpa only [continuousSup, Set.image_univ] using hx

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_coe_closedUnitBall_le_one
    (x : Metric.closedBall (0 : E) 1) : ‖(x : E)‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using x.property

omit [FiniteDimensional ℝ E] in
private theorem exists_unitSphere_radialRepresentation [Nontrivial E]
    (x : Metric.closedBall (0 : E) 1) (hx : (x : E) ≠ 0) :
    ∃ u : Metric.sphere (0 : E) 1,
      (x : E) = ‖(x : E)‖ • (u : E) := by
  let u : Metric.sphere (0 : E) 1 :=
    ⟨(‖(x : E)‖⁻¹ : ℝ) • (x : E), by
      rw [Metric.mem_sphere, dist_zero_right]
      exact norm_smul_inv_norm hx⟩
  refine ⟨u, ?_⟩
  change (x : E) = ‖(x : E)‖ • ((‖(x : E)‖⁻¹ : ℝ) • (x : E))
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- For a radially positively homogeneous path vanishing at zero, the
uniform norm on the closed unit ball is the supremum of its absolute value
on the unit sphere.
@isnad1 id=eq.2h2v.s9.e69a99413630 from=translated src=- shape=791e7b2a vocab=d0485ed6
-/
theorem norm_eq_unitSphereSupAbs [Nontrivial E]
    (f : C(Metric.closedBall (0 : E) 1, ℝ))
    (hzero : f (closedUnitBallZero (E := E)) = 0)
    (hhom : PositivelyHomogeneousOnClosedUnitBall f) :
    ‖f‖ = unitSphereSupAbs f := by
  letI : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  obtain ⟨umax, habs, hmax⟩ :=
    exists_continuousSup_eq_and_ge (unitSphereAbsContinuousMap f)
  have hsup_nonneg : 0 ≤ unitSphereSupAbs f := by
    rw [unitSphereSupAbs, habs]
    exact abs_nonneg _
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ hsup_nonneg]
    intro x
    simp only [Real.norm_eq_abs]
    by_cases hx : (x : E) = 0
    · have hxzero : x = closedUnitBallZero (E := E) := Subtype.ext hx
      rw [hxzero, hzero, abs_zero]
      exact hsup_nonneg
    · obtain ⟨u, hxu⟩ := exists_unitSphere_radialRepresentation x hx
      let us : Metric.closedBall (0 : E) 1 :=
        unitSphereInClosedUnitBall (E := E) u
      have hxu' : (x : E) = ‖(x : E)‖ • (us : E) := by
        simpa only [us, coe_unitSphereInClosedUnitBall] using hxu
      have hf : f x = ‖(x : E)‖ * f us :=
        hhom us x ‖(x : E)‖ (norm_nonneg _) hxu'
      have hu_le : |f us| ≤ unitSphereSupAbs f := by
        rw [unitSphereSupAbs, habs]
        simpa only [us, unitSphereAbsContinuousMap_apply] using hmax u
      rw [hf, abs_mul, abs_of_nonneg (norm_nonneg (x : E))]
      exact (mul_le_mul_of_nonneg_right
        (norm_coe_closedUnitBall_le_one x) (abs_nonneg (f us))).trans
          (by simpa only [one_mul] using hu_le)
  · rw [unitSphereSupAbs, habs]
    simpa only [unitSphereAbsContinuousMap_apply, Real.norm_eq_abs] using
      f.norm_coe_le_norm
        (unitSphereInClosedUnitBall (E := E) umax)

/-- For a radially positively homogeneous path vanishing at zero, its
maximum on the closed unit ball is the supremum of its positive part on the
unit sphere.
@isnad1 id=eq.2h2v.s8.eba62856dc91 from=translated src=- shape=3f00392a vocab=fe5d4e7a
-/
theorem continuousSup_eq_unitSphereSupPositivePart [Nontrivial E]
    (f : C(Metric.closedBall (0 : E) 1, ℝ))
    (hzero : f (closedUnitBallZero (E := E)) = 0)
    (hhom : PositivelyHomogeneousOnClosedUnitBall f) :
    continuousSup f = unitSphereSupPositivePart f := by
  letI : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  obtain ⟨xmax, hball, hballMax⟩ :=
    exists_continuousSup_eq_and_ge f
  obtain ⟨umax, hpos, hposMax⟩ :=
    exists_continuousSup_eq_and_ge
      (unitSpherePositivePartContinuousMap f)
  have hpos_nonneg : 0 ≤ unitSphereSupPositivePart f := by
    rw [unitSphereSupPositivePart, hpos]
    exact le_max_right _ _
  apply le_antisymm
  · rw [hball]
    by_cases hx : (xmax : E) = 0
    · have hxzero : xmax = closedUnitBallZero (E := E) := Subtype.ext hx
      rw [hxzero, hzero]
      exact hpos_nonneg
    · obtain ⟨u, hxu⟩ := exists_unitSphere_radialRepresentation xmax hx
      let us : Metric.closedBall (0 : E) 1 :=
        unitSphereInClosedUnitBall (E := E) u
      have hxu' : (xmax : E) = ‖(xmax : E)‖ • (us : E) := by
        simpa only [us, coe_unitSphereInClosedUnitBall] using hxu
      have hf : f xmax = ‖(xmax : E)‖ * f us :=
        hhom us xmax ‖(xmax : E)‖ (norm_nonneg _) hxu'
      have hmul : ‖(xmax : E)‖ * f us ≤ max (f us) 0 := by
        by_cases hu : f us ≤ 0
        · exact (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hu).trans
            (le_max_right _ _)
        · exact (mul_le_mul_of_nonneg_right
            (norm_coe_closedUnitBall_le_one xmax) (lt_of_not_ge hu).le).trans
              (by simpa only [one_mul] using (le_max_left (f us) 0))
      calc
        f xmax = ‖(xmax : E)‖ * f us := hf
        _ ≤ max (f us) 0 := hmul
        _ ≤ unitSphereSupPositivePart f := by
          rw [unitSphereSupPositivePart, hpos]
          simpa only [us, unitSpherePositivePartContinuousMap_apply] using
            hposMax u
  · rw [unitSphereSupPositivePart, hpos]
    change max
      (f (unitSphereInClosedUnitBall (E := E) umax)) 0 ≤ continuousSup f
    apply max_le
    · rw [hball]
      exact hballMax (unitSphereInClosedUnitBall (E := E) umax)
    · rw [hball]
      have hzero_le := hballMax (closedUnitBallZero (E := E))
      rw [hzero] at hzero_le
      exact hzero_le

/-- The reverse one-sided functional is the supremum of the positive part of
the negative path on the unit sphere.
@isnad1 id=eq.2h2v.s9.35f83e521b3e from=translated src=- shape=f5870c33 vocab=9242f79a
-/
theorem continuousSup_neg_eq_unitSphereSupNegativePart [Nontrivial E]
    (f : C(Metric.closedBall (0 : E) 1, ℝ))
    (hzero : f (closedUnitBallZero (E := E)) = 0)
    (hhom : PositivelyHomogeneousOnClosedUnitBall f) :
    continuousSup (-f) = unitSphereSupNegativePart f := by
  have hzero_neg : (-f) (closedUnitBallZero (E := E)) = 0 := by
    simp only [ContinuousMap.neg_apply, hzero, neg_zero]
  have hhom_neg : PositivelyHomogeneousOnClosedUnitBall (-f) := by
    intro x y r hr hxy
    have h := hhom x y r hr hxy
    change -f y = r * -f x
    rw [h]
    ring
  exact continuousSup_eq_unitSphereSupPositivePart (-f) hzero_neg hhom_neg

/-- The three deterministic limit functionals in the pointwise random-set
CLT, rewritten exactly as suprema over the unit sphere.
@isnad1 id=and.2h2v.s9.1660bde73825 from=translated src=- shape=356feabd vocab=eecee70b
-/
theorem pointwiseContinuousMappings_eq_unitSphere [Nontrivial E]
    (f : C(Metric.closedBall (0 : E) 1, ℝ))
    (hzero : f (closedUnitBallZero (E := E)) = 0)
    (hhom : PositivelyHomogeneousOnClosedUnitBall f) :
    ‖f‖ = unitSphereSupAbs f ∧
      continuousSup f = unitSphereSupPositivePart f ∧
      continuousSup (-f) = unitSphereSupNegativePart f :=
  ⟨norm_eq_unitSphereSupAbs f hzero hhom,
    continuousSup_eq_unitSphereSupPositivePart f hzero hhom,
    continuousSup_neg_eq_unitSphereSupNegativePart f hzero hhom⟩

/-- The three set-valued continuous-mapping conclusions generated by one
functional weak limit of the scaled support-difference process.

The first component is the symmetric Hausdorff limit.  The second and third
components are respectively the directed distances from the empirical set to
the population set and in the reverse direction.  The symmetric scaling is
written with `|c i|`; the two directed statements use the supplied
nonnegative scale `c i` directly.
@isnad1 id=and.8h13v.s10.33c9ead7ed2c from=translated src=- shape=e0ef2732 vocab=821605e9
-/
theorem pointwiseRandomSetCLT_of_supportProcess
    {I Ω' : Type*} {Ω : I → Type*}
    {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ']
    [MeasurableSpace C(closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(closedBall (0 : E) 1, ℝ)]
    (c : I → ℝ) (K : (i : I) → Ω i → Set E) (L : Set E)
    (Z : Ω' → C(closedBall (0 : E) 1, ℝ))
    (hc : ∀ i, 0 ≤ c i)
    (hKcompact : ∀ i ω, IsCompact (K i ω))
    (hKne : ∀ i ω, (K i ω).Nonempty)
    (hKconv : ∀ i ω, Convex ℝ (K i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hLconv : Convex ℝ L)
    {l : Filter I}
    (hprocess : TendstoInDistribution
      (fun i ω => scaledSupportDifferenceContinuousMap
        (c i) (K i ω) L (hKcompact i ω) hLcompact
          (hKne i ω) hLne)
      l Z μ μ') :
    TendstoInDistribution
        (fun i ω => |c i| * hausdorffDist (K i ω) L)
        l (fun ω => ‖Z ω‖) μ μ' ∧
      TendstoInDistribution
        (fun i ω => c i * directedHausdorffDist (K i ω) L)
        l (fun ω => continuousSup (Z ω)) μ μ' ∧
      TendstoInDistribution
        (fun i ω => c i * directedHausdorffDist L (K i ω))
        l (fun ω => continuousSup (-Z ω)) μ μ' := by
  refine ⟨?_, ?_, ?_⟩
  · exact tendstoInDistribution_absScale_mul_hausdorffDist_of_process
      c K L Z hKcompact hKne hKconv hLcompact hLne hLconv hprocess
  · exact tendstoInDistribution_scale_mul_directedHausdorffDist_of_process
      c K L Z hc hKcompact hKne hLcompact hLne hLconv hprocess
  · exact
      tendstoInDistribution_scale_mul_reverseDirectedHausdorffDist_of_process
        c K L Z hc hKcompact hKne hKconv hLcompact hLne hprocess

/-- The pointwise random-set CLT with the three limit variables written in
the literal sphere form used in the report.  The additional pathwise
hypotheses say that the limiting support process vanishes at the zero
direction and remains positively homogeneous along every ray of the closed
unit ball.
@isnad1 id=and.10h13v.s10.c7fc38390914 from=translated src=- shape=121d2a15 vocab=6ca1fef8
-/
theorem pointwiseRandomSetCLT_of_supportProcess_unitSphere [Nontrivial E]
    {I Ω' : Type*} {Ω : I → Type*}
    {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ']
    [MeasurableSpace C(closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(closedBall (0 : E) 1, ℝ)]
    (c : I → ℝ) (K : (i : I) → Ω i → Set E) (L : Set E)
    (Z : Ω' → C(closedBall (0 : E) 1, ℝ))
    (hc : ∀ i, 0 ≤ c i)
    (hKcompact : ∀ i ω, IsCompact (K i ω))
    (hKne : ∀ i ω, (K i ω).Nonempty)
    (hKconv : ∀ i ω, Convex ℝ (K i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hLconv : Convex ℝ L)
    (hZzero : ∀ ω, Z ω (closedUnitBallZero (E := E)) = 0)
    (hZhom : ∀ ω, PositivelyHomogeneousOnClosedUnitBall (Z ω))
    {l : Filter I}
    (hprocess : TendstoInDistribution
      (fun i ω => scaledSupportDifferenceContinuousMap
        (c i) (K i ω) L (hKcompact i ω) hLcompact
          (hKne i ω) hLne)
      l Z μ μ') :
    TendstoInDistribution
        (fun i ω => |c i| * hausdorffDist (K i ω) L)
        l (fun ω => unitSphereSupAbs (Z ω)) μ μ' ∧
      TendstoInDistribution
        (fun i ω => c i * directedHausdorffDist (K i ω) L)
        l (fun ω => unitSphereSupPositivePart (Z ω)) μ μ' ∧
      TendstoInDistribution
        (fun i ω => c i * directedHausdorffDist L (K i ω))
        l (fun ω => unitSphereSupNegativePart (Z ω)) μ μ' := by
  obtain ⟨hsymmetric, hforward, hreverse⟩ :=
    pointwiseRandomSetCLT_of_supportProcess
      c K L Z hc hKcompact hKne hKconv hLcompact hLne hLconv hprocess
  have hsymmetricLimit :
      (fun ω ↦ ‖Z ω‖) = (fun ω ↦ unitSphereSupAbs (Z ω)) := by
    funext ω
    exact norm_eq_unitSphereSupAbs (Z ω) (hZzero ω) (hZhom ω)
  have hforwardLimit :
      (fun ω ↦ continuousSup (Z ω)) =
        (fun ω ↦ unitSphereSupPositivePart (Z ω)) := by
    funext ω
    exact continuousSup_eq_unitSphereSupPositivePart
      (Z ω) (hZzero ω) (hZhom ω)
  have hreverseLimit :
      (fun ω ↦ continuousSup (-Z ω)) =
        (fun ω ↦ unitSphereSupNegativePart (Z ω)) := by
    funext ω
    exact continuousSup_neg_eq_unitSphereSupNegativePart
      (Z ω) (hZzero ω) (hZhom ω)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsymmetricLimit]
    exact hsymmetric
  · rw [← hforwardLimit]
    exact hforward
  · rw [← hreverseLimit]
    exact hreverse

end RandomSetTheory
