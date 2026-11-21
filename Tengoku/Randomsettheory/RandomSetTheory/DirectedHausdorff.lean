/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.SupportProcessContinuousMapping

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directed Hausdorff distance and one-sided support processes

For nonempty compact convex sets in a finite-dimensional real inner-product
space, the directed Hausdorff distance from `K` to `L` is the maximum of
`supportFunction K u - supportFunction L u` over the closed unit ball.  The
maximum is automatically nonnegative because the zero direction is present.

This is the deterministic identity behind the two one-sided limits in the
pointwise random-set CLT from Section 5 of the report.  The final theorem is a
continuous-mapping result: it turns a separately supplied functional weak
limit of the support-difference process into a weak limit for directed
Hausdorff distance.  It deliberately does not prove the functional CLT or its
tightness premise.
-/

open Real Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ProbabilityTheory Pointwise

noncomputable section

namespace RandomSetTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Directed Hausdorff distance from `K` to `L`, written as the largest
point-to-set distance attained on `K`.  The definition is total; the classical
geometric theorems below assume that both sets are nonempty and compact.-/
def directedHausdorffDist (K L : Set E) : ℝ :=
  sSup ((fun x => infDist x L) '' K)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Compactness of `K` makes the directed distance attain its maximum.
@isnad1 id=ex.2h3v.s5.4f762c2bb5f2 from=translated src=- shape=7d032097 vocab=e8166575
-/
theorem exists_mem_infDist_eq_directedHausdorffDist
    {K L : Set E} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ x ∈ K, infDist x L = directedHausdorffDist K L := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_sSup_image_eq hKne
    ((continuous_infDist_pt L).continuousOn :
      ContinuousOn (fun x => infDist x L) K)
  exact ⟨x, hx, hmax.symm⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Every point-to-set distance on `K` is bounded by the directed Hausdorff
distance.
@isnad1 id=le.2h4v.s5.e1407e86d675 from=translated src=- shape=3fec64bf vocab=a191ca40
-/
theorem infDist_le_directedHausdorffDist
    {K L : Set E} (hK : IsCompact K)
    {x : E} (hx : x ∈ K) :
    infDist x L ≤ directedHausdorffDist K L := by
  unfold directedHausdorffDist
  exact le_csSup (hK.image (continuous_infDist_pt L)).bddAbove
    (mem_image_of_mem _ hx)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Directed Hausdorff distance is nonnegative when its source is nonempty.
@isnad1 id=le.2h3v.s5.5fd950f5293f from=translated src=- shape=a0a720b8 vocab=3f5ed3e2
-/
theorem directedHausdorffDist_nonneg
    {K L : Set E} (hK : IsCompact K) (hKne : K.Nonempty) :
    0 ≤ directedHausdorffDist K L := by
  obtain ⟨x, hx⟩ := hKne
  exact infDist_nonneg.trans
    (infDist_le_directedHausdorffDist hK hx)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- One orientation of the Hausdorff distance is bounded by the symmetric
Hausdorff distance.
@isnad1 id=le.4h3v.s5.6d1893482827 from=translated src=- shape=84e06fde vocab=554d59c0
-/
theorem directedHausdorffDist_le_hausdorffDist
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    directedHausdorffDist K L ≤ hausdorffDist K L := by
  obtain ⟨x, hx, hmax⟩ :=
    exists_mem_infDist_eq_directedHausdorffDist hK hKne (L := L)
  rw [← hmax]
  exact infDist_le_hausdorffDist_of_mem hx
    (hausdorffEDist_ne_top_of_nonempty_of_bounded
      hKne hLne hK.isBounded hL.isBounded)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Classical directed decomposition of Hausdorff distance.**  For two
nonempty compact sets, the symmetric Hausdorff distance is the maximum of
the two directed point-to-set distances.
@isnad1 id=eq.4h3v.s6.19c18657bd6d from=translated src=- shape=3751a8e8 vocab=12d48607
-/
theorem hausdorffDist_eq_max_directedHausdorffDist
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    hausdorffDist K L =
      max (directedHausdorffDist K L) (directedHausdorffDist L K) := by
  apply le_antisymm
  · have hr : 0 ≤
        max (directedHausdorffDist K L) (directedHausdorffDist L K) :=
      (directedHausdorffDist_nonneg hK hKne).trans
        (le_max_left _ _)
    apply hausdorffDist_le_of_infDist hr
    · intro x hx
      exact (infDist_le_directedHausdorffDist hK hx).trans
        (le_max_left _ _)
    · intro y hy
      exact (infDist_le_directedHausdorffDist hL hy).trans
        (le_max_right _ _)
  · apply max_le
    · exact directedHausdorffDist_le_hausdorffDist hK hL hKne hLne
    · simpa only [hausdorffDist_comm] using
        (directedHausdorffDist_le_hausdorffDist hL hK hLne hKne)

/-- The one-sided support gap on the closed unit ball.-/
def directedSupportGap (K L : Set E) : ℝ :=
  sSup ((fun u : E => supportFunction K u - supportFunction L u) ''
    Metric.closedBall 0 1)

omit [FiniteDimensional ℝ E] in
/-- The difference of the support functions of two nonempty compact sets is
continuous on the ambient inner-product space.-/
private theorem continuous_supportFunction_sub
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    Continuous (fun u : E => supportFunction K u - supportFunction L u) := by
  obtain ⟨RK, hRK⟩ := hK.isBounded.exists_norm_le
  obtain ⟨RL, hRL⟩ := hL.isBounded.exists_norm_le
  have hRK0 : 0 ≤ RK := by
    obtain ⟨x, hx⟩ := hKne
    exact (norm_nonneg x).trans (hRK x hx)
  have hRL0 : 0 ≤ RL := by
    obtain ⟨y, hy⟩ := hLne
    exact (norm_nonneg y).trans (hRL y hy)
  let C : NNReal := ⟨RK + RL, add_nonneg hRK0 hRL0⟩
  apply (LipschitzWith.of_dist_le_mul (K := C) ?_).continuous
  intro u v
  rw [show (C : ℝ) = RK + RL by rfl]
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
      (abs_supportFunctionDifference_sub_le
        hK hL hKne hLne hRK hRL u v)

/-- The zero direction shows that the directed support gap is nonnegative.
@isnad1 id=le.4h3v.s6.9570ed50c93b from=translated src=- shape=6e452400 vocab=b11fe1b7
-/
theorem directedSupportGap_nonneg
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    0 ≤ directedSupportGap K L := by
  unfold directedSupportGap
  have hcompact : IsCompact
      ((fun u : E => supportFunction K u - supportFunction L u) ''
        Metric.closedBall 0 1) := by
    exact (isCompact_closedBall (0 : E) 1).image
      (continuous_supportFunction_sub hK hL hKne hLne)
  have hzero : 0 ∈
      (fun u : E => supportFunction K u - supportFunction L u) ''
        Metric.closedBall 0 1 := by
    refine ⟨0, by simp, ?_⟩
    simp [supportFunction_zero hK hKne, supportFunction_zero hL hLne]
  exact (le_csSup hcompact.bddAbove hzero)

/-- Any directional support difference on the unit ball is bounded by the
directed support gap.
@isnad1 id=le.5h4v.s6.c0d6aef1b443 from=translated src=- shape=caa38f40 vocab=89c8e5c0
-/
theorem supportFunction_sub_le_directedSupportGap
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    {u : E} (hu : ‖u‖ ≤ 1) :
    supportFunction K u - supportFunction L u ≤ directedSupportGap K L := by
  unfold directedSupportGap
  have hcompact : IsCompact
      ((fun v : E => supportFunction K v - supportFunction L v) ''
        Metric.closedBall 0 1) := by
    exact (isCompact_closedBall (0 : E) 1).image
      (continuous_supportFunction_sub hK hL hKne hLne)
  apply le_csSup hcompact.bddAbove
  exact ⟨u, by simpa [Metric.mem_closedBall, dist_zero_right] using hu, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- Support differences are bounded above by the directed Hausdorff distance.
This is the one-sided counterpart of the elementary support/Hausdorff bound.
@isnad1 id=le.4h4v.s6.b6c9dc370833 from=translated src=- shape=442a1114 vocab=7a3809a5
-/
theorem supportFunction_sub_le_directedHausdorffDist
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) (u : E) :
    supportFunction K u - supportFunction L u ≤
      ‖u‖ * directedHausdorffDist K L := by
  obtain ⟨x, hx, hxsup⟩ := supportFunction_attains hK hKne u
  obtain ⟨y, hy, hxy⟩ := hL.exists_infDist_eq_dist hLne x
  have hdist : dist x y ≤ directedHausdorffDist K L := by
    rw [← hxy]
    exact infDist_le_directedHausdorffDist hK hx
  have hinner : ⟪u, y⟫_ℝ ≤ supportFunction L u :=
    inner_le_supportFunction hL hy u
  calc
    supportFunction K u - supportFunction L u =
        ⟪u, x⟫_ℝ - supportFunction L u := by rw [hxsup]
    _ ≤ ⟪u, x⟫_ℝ - ⟪u, y⟫_ℝ := sub_le_sub_left hinner _
    _ = ⟪u, x - y⟫_ℝ := (inner_sub_right _ _ _).symm
    _ ≤ |⟪u, x - y⟫_ℝ| := le_abs_self _
    _ ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ = ‖u‖ * dist x y := by rw [dist_eq_norm]
    _ ≤ ‖u‖ * directedHausdorffDist K L :=
      mul_le_mul_of_nonneg_left hdist (norm_nonneg _)

omit [FiniteDimensional ℝ E] in
/-- The directed support gap never exceeds the directed Hausdorff distance.
@isnad1 id=le.4h3v.s6.ce4cb9637b7e from=translated src=- shape=695addd0 vocab=d3e95d90
-/
theorem directedSupportGap_le_directedHausdorffDist
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    directedSupportGap K L ≤ directedHausdorffDist K L := by
  unfold directedSupportGap
  apply csSup_le
  · exact ⟨0, by
      refine ⟨0, by simp, ?_⟩
      simp [supportFunction_zero hK hKne, supportFunction_zero hL hLne]⟩
  · rintro z ⟨u, hu, rfl⟩
    have hu' : ‖u‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hu
    calc
      supportFunction K u - supportFunction L u ≤
          ‖u‖ * directedHausdorffDist K L :=
        supportFunction_sub_le_directedHausdorffDist hK hL hKne hLne u
      _ ≤ 1 * directedHausdorffDist K L :=
        mul_le_mul_of_nonneg_right hu'
          (directedHausdorffDist_nonneg hK hKne)
      _ = directedHausdorffDist K L := one_mul _

omit [FiniteDimensional ℝ E] in
/-- At a nearest point in a compact convex target, the displacement vector
supports the target.-/
private theorem supportFunction_displacement_eq_inner_nearest
    {L : Set E} (hL : IsCompact L) (hLne : L.Nonempty)
    (hLconv : Convex ℝ L) {x y : E} (hy : y ∈ L)
    (hxy : infDist x L = dist x y) :
    supportFunction L (x - y) = ⟪x - y, y⟫_ℝ := by
  have hmin : ‖x - y‖ = ⨅ z : L, ‖x - z‖ := by
    rw [← dist_eq_norm, ← hxy, infDist_eq_iInf]
    congr 1
    funext z
    rw [dist_eq_norm]
  have hproj : ∀ z ∈ L, ⟪x - y, z - y⟫_ℝ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hLconv hy).mp hmin
  apply le_antisymm
  · obtain ⟨z, hz, hatt⟩ := supportFunction_attains hL hLne (x - y)
    rw [hatt]
    have hzproj := hproj z hz
    rw [inner_sub_right] at hzproj
    linarith
  · exact inner_le_supportFunction hL hy (x - y)

/-- The maximal point-to-set distance is witnessed by a unit direction whose
support gap is at least that distance.
@isnad1 id=le.5h3v.s7.2fe6c7d8dc09 from=translated src=- shape=d17e0816 vocab=73815b22
-/
theorem directedHausdorffDist_le_directedSupportGap
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) (hLconv : Convex ℝ L) :
    directedHausdorffDist K L ≤ directedSupportGap K L := by
  obtain ⟨x, hx, hxd⟩ :=
    exists_mem_infDist_eq_directedHausdorffDist hK hKne (L := L)
  obtain ⟨y, hy, hxy⟩ := hL.exists_infDist_eq_dist hLne x
  by_cases hzero : ‖x - y‖ = 0
  · have hd0 : directedHausdorffDist K L = 0 := by
      rw [← hxd, hxy, dist_eq_norm, hzero]
    rw [hd0]
    exact directedSupportGap_nonneg hK hL hKne hLne
  · let u : E := ‖x - y‖⁻¹ • (x - y)
    have hnormpos : 0 < ‖x - y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have huNorm : ‖u‖ = 1 := by
      change ‖‖x - y‖⁻¹ • (x - y)‖ = 1
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hnormpos), inv_mul_cancel₀ hzero]
    have huBall : ‖u‖ ≤ 1 := huNorm.le
    have hsupportL : supportFunction L u = ⟪u, y⟫_ℝ := by
      calc
        supportFunction L u = ‖x - y‖⁻¹ * supportFunction L (x - y) := by
          change supportFunction L (‖x - y‖⁻¹ • (x - y)) = _
          rw [supportFunction_smul_direction hL hLne
            (inv_nonneg.mpr hnormpos.le)]
        _ = ‖x - y‖⁻¹ * ⟪x - y, y⟫_ℝ := by
          rw [supportFunction_displacement_eq_inner_nearest
            hL hLne hLconv hy hxy]
        _ = ⟪u, y⟫_ℝ := by
          change _ = ⟪‖x - y‖⁻¹ • (x - y), y⟫_ℝ
          rw [real_inner_smul_left]
    have hsupportX : ⟪u, x⟫_ℝ ≤ supportFunction K u :=
      inner_le_supportFunction hK hx u
    have hgap : ‖x - y‖ ≤
        supportFunction K u - supportFunction L u := by
      rw [hsupportL]
      calc
        ‖x - y‖ = ⟪u, x - y⟫_ℝ := by
          change ‖x - y‖ = ⟪‖x - y‖⁻¹ • (x - y), x - y⟫_ℝ
          rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
          field_simp
        _ = ⟪u, x⟫_ℝ - ⟪u, y⟫_ℝ := inner_sub_right _ _ _
        _ ≤ supportFunction K u - ⟪u, y⟫_ℝ :=
          sub_le_sub_right hsupportX _
    calc
      directedHausdorffDist K L = ‖x - y‖ := by
        rw [← hxd, hxy, dist_eq_norm]
      _ ≤ supportFunction K u - supportFunction L u := hgap
      _ ≤ directedSupportGap K L :=
        supportFunction_sub_le_directedSupportGap
          hK hL hKne hLne huBall

/-- **Directed support/Hausdorff duality.**  For compact nonempty sets, with
the target convex, directed Hausdorff distance is exactly the maximum support
difference on the closed unit ball.  Convexity of the source is unnecessary.
@isnad1 id=eq.5h3v.s7.5db532e30024 from=translated src=- shape=d17e0816 vocab=6773d8f2
-/
theorem directedSupportGap_eq_directedHausdorffDist
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) (hLconv : Convex ℝ L) :
    directedSupportGap K L = directedHausdorffDist K L := by
  apply le_antisymm
  · exact directedSupportGap_le_directedHausdorffDist hK hL hKne hLne
  · exact directedHausdorffDist_le_directedSupportGap
      hK hL hKne hLne hLconv

/-- For compact nonempty convex sets, the usual support/Hausdorff duality
splits into the maximum of its two one-sided support gaps.
@isnad1 id=eq.6h3v.s8.6ed504663c6c from=translated src=- shape=74f1bfe5 vocab=2ed46fdb
-/
theorem hausdorffDist_eq_max_directedSupportGap
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) :
    hausdorffDist K L =
      max (directedSupportGap K L) (directedSupportGap L K) := by
  rw [directedSupportGap_eq_directedHausdorffDist
      hK hL hKne hLne hLconv,
    directedSupportGap_eq_directedHausdorffDist
      hL hK hLne hKne hKconv]
  exact hausdorffDist_eq_max_directedHausdorffDist hK hL hKne hLne

section ContinuousSup

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

/-- Maximum value of a continuous real function on a compact space.-/
def continuousSup (f : C(T, ℝ)) : ℝ := sSup (Set.range f)

/-- Taking the maximum of a continuous function on a compact index space is
continuous for the uniform topology.
@isnad1 id=continuo.0h1v.s5.861e2f3fba4b from=translated src=- shape=f1a1a94c vocab=91d39ac9
-/
theorem continuous_continuousSup :
    Continuous (continuousSup : C(T, ℝ) → ℝ) := by
  have heval : Continuous (fun p : C(T, ℝ) × T => p.1 p.2) := by fun_prop
  change Continuous (fun f : C(T, ℝ) => sSup (Set.range f))
  simpa only [Set.image_univ] using
    (isCompact_univ.continuous_sSup heval)

omit [CompactSpace T] in
/-- A nonnegative scalar can be pulled through the maximum of a continuous
real function on a compact space.
@isnad1 id=eq.1h3v.s6.23c969189602 from=translated src=- shape=c7f080b8 vocab=6dd72a68
-/
theorem continuousSup_smul_of_nonneg
    (c : ℝ) (hc : 0 ≤ c) (f : C(T, ℝ)) :
    continuousSup (c • f) = c * continuousSup f := by
  unfold continuousSup
  have hrange : Set.range (c • f) = c • Set.range f := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact Set.mem_smul_set.mpr ⟨f u, ⟨u, rfl⟩, by simp⟩
    · rintro hz
      rcases Set.mem_smul_set.mp hz with ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, by simp⟩
  rw [hrange, Real.sSup_smul_of_nonneg hc]
  rfl

/-- Continuous-mapping transfer for the supremum (without absolute values)
of a compactly indexed continuous process.
@isnad1 id=tendstoi.1h11v.s7.80bc2f75d6d9 from=translated src=- shape=32051e03 vocab=82e9ef4f
-/
theorem TendstoInDistribution.continuousSup
    {I Omega' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Omega'} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu']
    [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
    {X : (i : I) → Omega i → C(T, ℝ)} {Z : Omega' → C(T, ℝ)}
    {l : Filter I} (h : TendstoInDistribution X l Z mu mu') :
    TendstoInDistribution
      (fun i => continuousSup ∘ X i) l
      (continuousSup ∘ Z) mu mu' :=
  h.continuous_comp continuous_continuousSup

end ContinuousSup

section DirectedContinuousMapping

/-- The maximum of the support-difference path is directed Hausdorff
distance.
@isnad1 id=eq.5h3v.s8.f1bb5e97b165 from=translated src=- shape=0b5e19ca vocab=38074716
-/
theorem continuousSup_supportDifferenceContinuousMap_eq_directedHausdorffDist
    (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) (hLconv : Convex ℝ L) :
    continuousSup (supportDifferenceContinuousMap K L hK hL hKne hLne) =
      directedHausdorffDist K L := by
  rw [← directedSupportGap_eq_directedHausdorffDist
    hK hL hKne hLne hLconv]
  unfold continuousSup directedSupportGap
  congr 1
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, u.property, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

/-- Functional continuous-mapping bridge for directed Hausdorff distance.
The premise is a weak limit for the entire scaled support-difference process;
no Donsker or tightness theorem is claimed.
@isnad1 id=tendstoi.7h13v.s9.f670cbc880bf from=translated src=- shape=688bcfde vocab=34ecd4d5
-/
theorem tendstoInDistribution_scale_mul_directedHausdorffDist_of_process
    {I Omega' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Omega'} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu']
    [MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    (c : I → ℝ) (K : (i : I) → Omega i → Set E) (L : Set E)
    (Z : Omega' → C(Metric.closedBall (0 : E) 1, ℝ))
    (hc : ∀ i, 0 ≤ c i)
    (hKcompact : ∀ i omega, IsCompact (K i omega))
    (hKne : ∀ i omega, (K i omega).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    {l : Filter I}
    (hprocess : TendstoInDistribution
      (fun i omega => scaledSupportDifferenceContinuousMap
        (c i) (K i omega) L (hKcompact i omega) hLcompact
          (hKne i omega) hLne)
      l Z mu mu') :
    TendstoInDistribution
      (fun i omega => c i * directedHausdorffDist (K i omega) L)
      l (fun omega => continuousSup (Z omega)) mu mu' := by
  have hsup := RandomSetTheory.TendstoInDistribution.continuousSup hprocess
  apply hsup.congr
  · intro i
    filter_upwards [] with omega
    change continuousSup (scaledSupportDifferenceContinuousMap
      (c i) (K i omega) L (hKcompact i omega) hLcompact
        (hKne i omega) hLne) =
      c i * directedHausdorffDist (K i omega) L
    unfold scaledSupportDifferenceContinuousMap
    rw [continuousSup_smul_of_nonneg (c i) (hc i)]
    rw [continuousSup_supportDifferenceContinuousMap_eq_directedHausdorffDist
      (K i omega) L (hKcompact i omega) hLcompact
      (hKne i omega) hLne hLconv]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Reverse-orientation version of the preceding continuous-mapping theorem.
The limit is the supremum of the negative support process, corresponding to
the negative part in the second one-sided limit from the report.
@isnad1 id=tendstoi.7h13v.s10.916dbfcc48b6 from=translated src=- shape=f71abb4f vocab=89c00d98
-/
theorem tendstoInDistribution_scale_mul_reverseDirectedHausdorffDist_of_process
    {I Omega' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Omega'} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu']
    [MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    (c : I → ℝ) (K : (i : I) → Omega i → Set E) (L : Set E)
    (Z : Omega' → C(Metric.closedBall (0 : E) 1, ℝ))
    (hc : ∀ i, 0 ≤ c i)
    (hKcompact : ∀ i omega, IsCompact (K i omega))
    (hKne : ∀ i omega, (K i omega).Nonempty)
    (hKconv : ∀ i omega, Convex ℝ (K i omega))
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    {l : Filter I}
    (hprocess : TendstoInDistribution
      (fun i omega => scaledSupportDifferenceContinuousMap
        (c i) (K i omega) L (hKcompact i omega) hLcompact
          (hKne i omega) hLne)
      l Z mu mu') :
    TendstoInDistribution
      (fun i omega => c i * directedHausdorffDist L (K i omega))
      l (fun omega => continuousSup (-Z omega)) mu mu' := by
  have hneg : TendstoInDistribution
      (fun i omega => -scaledSupportDifferenceContinuousMap
        (c i) (K i omega) L (hKcompact i omega) hLcompact
          (hKne i omega) hLne)
      l (fun omega => -Z omega) mu mu' :=
    hprocess.continuous_comp continuous_neg
  have hsup := RandomSetTheory.TendstoInDistribution.continuousSup hneg
  apply hsup.congr
  · intro i
    filter_upwards [] with omega
    change continuousSup
      (-scaledSupportDifferenceContinuousMap
        (c i) (K i omega) L (hKcompact i omega) hLcompact
          (hKne i omega) hLne) =
      c i * directedHausdorffDist L (K i omega)
    have heq :
        -scaledSupportDifferenceContinuousMap
            (c i) (K i omega) L (hKcompact i omega) hLcompact
              (hKne i omega) hLne =
          c i • supportDifferenceContinuousMap L (K i omega)
            hLcompact (hKcompact i omega) hLne (hKne i omega) := by
      ext u
      simp only [scaledSupportDifferenceContinuousMap_apply,
        supportDifferenceContinuousMap_apply, ContinuousMap.neg_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      ring
    rw [heq, continuousSup_smul_of_nonneg (c i) (hc i)]
    rw [continuousSup_supportDifferenceContinuousMap_eq_directedHausdorffDist
      L (K i omega) hLcompact (hKcompact i omega)
      hLne (hKne i omega) (hKconv i omega)]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end DirectedContinuousMapping

end RandomSetTheory
