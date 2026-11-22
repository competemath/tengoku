/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.LimitTheorems

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform support-function transfer for parameterized set-valued maps

This file records the deterministic uniform step that is used after proving
uniform estimates for support-function processes.  For compact nonempty
convex fibers, a bound uniform in the parameter and in directions of the
closed unit ball is equivalent to the same uniform Hausdorff bound.

The convergence statements below use mathlib's genuine `TendstoUniformly`.
They are deterministic transfer principles; no probabilistic central limit
theorem is asserted here.
-/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal

noncomputable section

namespace RandomSetTheory

/-- Uniformly over a parameter family, the support Hausdorff gap and the
Hausdorff distance have exactly the same upper bounds.
@isnad1 id=iff.6h5v.s8.d64636d4a0a5 from=translated src=- shape=93b65071 vocab=bcd05dbc
-/
theorem forall_supportHausdorffGap_le_iff_forall_hausdorffDist_le
    {Theta E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Theta → Set E}
    (hKcompact : ∀ theta, IsCompact (K theta))
    (hLcompact : ∀ theta, IsCompact (L theta))
    (hKne : ∀ theta, (K theta).Nonempty)
    (hLne : ∀ theta, (L theta).Nonempty)
    (hKconv : ∀ theta, Convex ℝ (K theta))
    (hLconv : ∀ theta, Convex ℝ (L theta))
    (r : ℝ) :
    (∀ theta, supportHausdorffGap (K theta) (L theta) ≤ r) ↔
      ∀ theta, hausdorffDist (K theta) (L theta) ≤ r := by
  simp_rw [supportHausdorffGap_eq_hausdorffDist
    (hKcompact _) (hLcompact _) (hKne _) (hLne _)
    (hKconv _) (hLconv _)]

/-- A Hausdorff bound uniform in `theta` is equivalent to an absolute support
bound uniform jointly in `theta` and in directions of the closed unit ball.
@isnad1 id=iff.7h5v.s8.628c6a39c03c from=translated src=- shape=3868c8ba vocab=4427e49b
-/
theorem forall_hausdorffDist_le_iff_forall_unitBall_supportFunction_sub_le
    {Theta E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Theta → Set E}
    (hKcompact : ∀ theta, IsCompact (K theta))
    (hLcompact : ∀ theta, IsCompact (L theta))
    (hKne : ∀ theta, (K theta).Nonempty)
    (hLne : ∀ theta, (L theta).Nonempty)
    (hKconv : ∀ theta, Convex ℝ (K theta))
    (hLconv : ∀ theta, Convex ℝ (L theta))
    {r : ℝ} (hr : 0 ≤ r) :
    (∀ theta, hausdorffDist (K theta) (L theta) ≤ r) ↔
      ∀ theta (u : E), ‖u‖ ≤ 1 →
        |supportFunction (K theta) u - supportFunction (L theta) u| ≤ r := by
  constructor
  · intro h theta u hu
    calc
      |supportFunction (K theta) u - supportFunction (L theta) u| ≤
          ‖u‖ * hausdorffDist (K theta) (L theta) :=
        abs_supportFunction_sub_le_hausdorffDist
          (hKcompact theta) (hLcompact theta) (hKne theta) (hLne theta) u
      _ ≤ 1 * r := mul_le_mul hu (h theta) hausdorffDist_nonneg (by norm_num)
      _ = r := one_mul r
  · intro h theta
    exact hausdorffDist_le_of_unitBall_supportFunction_sub_le
      (hKcompact theta) (hLcompact theta) (hKne theta) (hLne theta)
      (hKconv theta) (hLconv theta) hr (h theta)

/-- A pointwise rate envelope for all parameter-direction support errors is
also a rate envelope for every parameterwise Hausdorff distance.
@isnad1 id=le.8h8v.s8.5ba5919df39e from=translated src=- shape=1171fa91 vocab=4427e49b
-/
theorem uniform_hausdorffDist_le_of_unitBall_supportFunction_le
    {I Theta E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : I → Theta → Set E} {r : I → ℝ}
    (hKcompact : ∀ i theta, IsCompact (K i theta))
    (hLcompact : ∀ i theta, IsCompact (L i theta))
    (hKne : ∀ i theta, (K i theta).Nonempty)
    (hLne : ∀ i theta, (L i theta).Nonempty)
    (hKconv : ∀ i theta, Convex ℝ (K i theta))
    (hLconv : ∀ i theta, Convex ℝ (L i theta))
    (hr : ∀ i, 0 ≤ r i)
    (hsupport : ∀ i theta (u : E), ‖u‖ ≤ 1 →
      |supportFunction (K i theta) u - supportFunction (L i theta) u| ≤ r i) :
    ∀ i theta, hausdorffDist (K i theta) (L i theta) ≤ r i := by
  intro i
  exact (forall_hausdorffDist_le_iff_forall_unitBall_supportFunction_sub_le
    (hKcompact i) (hLcompact i) (hKne i) (hLne i)
    (hKconv i) (hLconv i) (hr i)).mpr (hsupport i)

/-- Uniform Hausdorff convergence of compact convex fibers is equivalent to
uniform convergence to zero of the signed support-function differences,
jointly over the parameter and the closed unit ball.
@isnad1 id=iff.6h6v.s9.0f8e72801d96 from=translated src=- shape=227174c4 vocab=de7f4016
-/
theorem tendstoUniformly_hausdorffDist_zero_iff_supportFunction_sub_zero
    {I Theta E : Type*} {l : Filter I}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : I → Theta → Set E}
    (hKcompact : ∀ i theta, IsCompact (K i theta))
    (hLcompact : ∀ i theta, IsCompact (L i theta))
    (hKne : ∀ i theta, (K i theta).Nonempty)
    (hLne : ∀ i theta, (L i theta).Nonempty)
    (hKconv : ∀ i theta, Convex ℝ (K i theta))
    (hLconv : ∀ i theta, Convex ℝ (L i theta)) :
    TendstoUniformly
        (fun i theta ↦ hausdorffDist (K i theta) (L i theta))
        (fun _ ↦ (0 : ℝ)) l ↔
      TendstoUniformly
        (fun i (p : Theta × Metric.closedBall (0 : E) 1) ↦
          supportFunction (K i p.1) p.2 - supportFunction (L i p.1) p.2)
        (fun _ ↦ (0 : ℝ)) l := by
  rw [tendstoUniformly_iff, tendstoUniformly_iff]
  constructor
  · intro h eps heps
    filter_upwards [h eps heps] with i hi
    rintro ⟨theta, u⟩
    have hu : ‖(u : E)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
    have hs := abs_supportFunction_sub_le_hausdorffDist
      (hKcompact i theta) (hLcompact i theta)
      (hKne i theta) (hLne i theta) (u : E)
    have hhd : hausdorffDist (K i theta) (L i theta) < eps := by
      simpa [Real.dist_eq, abs_of_nonneg hausdorffDist_nonneg] using hi theta
    have hmul : ‖(u : E)‖ * hausdorffDist (K i theta) (L i theta) < eps := by
      calc
        ‖(u : E)‖ * hausdorffDist (K i theta) (L i theta) ≤
            1 * hausdorffDist (K i theta) (L i theta) := by
          exact mul_le_mul_of_nonneg_right hu hausdorffDist_nonneg
        _ < eps := by simpa using hhd
    simpa [Real.dist_eq, abs_sub_comm] using hs.trans_lt hmul
  · intro h eps heps
    have heps2 : 0 < eps / 2 := half_pos heps
    filter_upwards [h (eps / 2) heps2] with i hi
    intro theta
    have hs : ∀ u : E, ‖u‖ ≤ 1 →
        |supportFunction (K i theta) u - supportFunction (L i theta) u| ≤
          eps / 2 := by
      intro u hu
      let v : Metric.closedBall (0 : E) 1 :=
        ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu⟩
      have hv := hi (theta, v)
      simpa [v, Real.dist_eq, abs_sub_comm] using le_of_lt hv
    have hhd := hausdorffDist_le_of_unitBall_supportFunction_sub_le
      (hKcompact i theta) (hLcompact i theta)
      (hKne i theta) (hLne i theta)
      (hKconv i theta) (hLconv i theta) heps2.le hs
    have hlt : hausdorffDist (K i theta) (L i theta) < eps :=
      hhd.trans_lt (half_lt_self heps)
    simpa [Real.dist_eq, abs_of_nonneg hausdorffDist_nonneg] using hlt

/-- If a nonnegative deterministic envelope tends to zero and dominates all
parameter-direction support errors, the Hausdorff distances converge to zero
uniformly in the parameter.
@isnad1 id=tendstou.9h7v.s8.a3756a2ffa1c from=translated src=- shape=366b4e19 vocab=499080e7
-/
theorem tendstoUniformly_hausdorffDist_zero_of_supportFunction_rate
    {I Theta E : Type*} {l : Filter I}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : I → Theta → Set E} {r : I → ℝ}
    (hKcompact : ∀ i theta, IsCompact (K i theta))
    (hLcompact : ∀ i theta, IsCompact (L i theta))
    (hKne : ∀ i theta, (K i theta).Nonempty)
    (hLne : ∀ i theta, (L i theta).Nonempty)
    (hKconv : ∀ i theta, Convex ℝ (K i theta))
    (hLconv : ∀ i theta, Convex ℝ (L i theta))
    (hr_nonneg : ∀ i, 0 ≤ r i)
    (hr : Tendsto r l (nhds 0))
    (hsupport : ∀ i theta (u : E), ‖u‖ ≤ 1 →
      |supportFunction (K i theta) u - supportFunction (L i theta) u| ≤ r i) :
    TendstoUniformly
      (fun i theta ↦ hausdorffDist (K i theta) (L i theta))
      (fun _ ↦ (0 : ℝ)) l := by
  rw [tendstoUniformly_iff]
  intro eps heps
  have hev : ∀ᶠ i in l, r i < eps := hr.eventually (Iio_mem_nhds heps)
  filter_upwards [hev] with i hi
  intro theta
  have hhd : hausdorffDist (K i theta) (L i theta) ≤ r i :=
    uniform_hausdorffDist_le_of_unitBall_supportFunction_le
      hKcompact hLcompact hKne hLne hKconv hLconv hr_nonneg hsupport i theta
  have hlt := hhd.trans_lt hi
  simpa [Real.dist_eq, abs_of_nonneg hausdorffDist_nonneg] using hlt

/-- Finite union bound for a parameter-uniform Hausdorff deviation.  The
input scalar events are the exact support Hausdorff gaps.
@isnad1 id=le.7h9v.s8.5dd70c8559b0 from=translated src=- shape=50715489 vocab=c999efe5
-/
theorem measure_exists_mem_hausdorffDist_gt_le_finset_supportHausdorffGap
    {Omega Theta E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} {K L : Omega → Theta → Set E}
    (hKcompact : ∀ omega theta, IsCompact (K omega theta))
    (hLcompact : ∀ omega theta, IsCompact (L omega theta))
    (hKne : ∀ omega theta, (K omega theta).Nonempty)
    (hLne : ∀ omega theta, (L omega theta).Nonempty)
    (hKconv : ∀ omega theta, Convex ℝ (K omega theta))
    (hLconv : ∀ omega theta, Convex ℝ (L omega theta))
    (s : Finset Theta) (r : ℝ) (delta : Theta → ℝ≥0∞)
    (htail : ∀ theta ∈ s,
      mu {omega | r < supportHausdorffGap (K omega theta) (L omega theta)} ≤
        delta theta) :
    mu {omega | ∃ theta ∈ s,
      r < hausdorffDist (K omega theta) (L omega theta)} ≤
      ∑ theta ∈ s, delta theta := by
  classical
  let A : Theta → Set Omega := fun theta ↦
    {omega | r < supportHausdorffGap (K omega theta) (L omega theta)}
  have hsub :
      {omega | ∃ theta ∈ s,
        r < hausdorffDist (K omega theta) (L omega theta)} ⊆
        ⋃ theta ∈ s, A theta := by
    rintro omega ⟨theta, htheta, hdev⟩
    refine Set.mem_iUnion.2 ⟨theta, Set.mem_iUnion.2 ⟨htheta, ?_⟩⟩
    change r < supportHausdorffGap (K omega theta) (L omega theta)
    rwa [supportHausdorffGap_eq_hausdorffDist
      (hKcompact omega theta) (hLcompact omega theta)
      (hKne omega theta) (hLne omega theta)
      (hKconv omega theta) (hLconv omega theta)]
  calc
    mu {omega | ∃ theta ∈ s,
        r < hausdorffDist (K omega theta) (L omega theta)} ≤
        mu (⋃ theta ∈ s, A theta) := measure_mono hsub
    _ ≤ ∑ theta ∈ s, mu (A theta) := measure_biUnion_finset_le s A
    _ ≤ ∑ theta ∈ s, delta theta := by
      exact Finset.sum_le_sum fun theta htheta ↦ htail theta htheta

/-- Countable union bound for a parameter-uniform Hausdorff deviation.
@isnad1 id=le.7h8v.s8.67b3bfd73994 from=translated src=- shape=f659d49e vocab=046f2e28
-/
theorem measure_exists_hausdorffDist_gt_le_tsum_supportHausdorffGap
    {Omega Theta E : Type*} [MeasurableSpace Omega] [Countable Theta]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} {K L : Omega → Theta → Set E}
    (hKcompact : ∀ omega theta, IsCompact (K omega theta))
    (hLcompact : ∀ omega theta, IsCompact (L omega theta))
    (hKne : ∀ omega theta, (K omega theta).Nonempty)
    (hLne : ∀ omega theta, (L omega theta).Nonempty)
    (hKconv : ∀ omega theta, Convex ℝ (K omega theta))
    (hLconv : ∀ omega theta, Convex ℝ (L omega theta))
    (r : ℝ) (delta : Theta → ℝ≥0∞)
    (htail : ∀ theta,
      mu {omega | r < supportHausdorffGap (K omega theta) (L omega theta)} ≤
        delta theta) :
    mu {omega | ∃ theta,
      r < hausdorffDist (K omega theta) (L omega theta)} ≤
      ∑' theta, delta theta := by
  let A : Theta → Set Omega := fun theta ↦
    {omega | r < supportHausdorffGap (K omega theta) (L omega theta)}
  have hsub :
      {omega | ∃ theta,
        r < hausdorffDist (K omega theta) (L omega theta)} ⊆
        ⋃ theta, A theta := by
    rintro omega ⟨theta, hdev⟩
    refine Set.mem_iUnion.2 ⟨theta, ?_⟩
    change r < supportHausdorffGap (K omega theta) (L omega theta)
    rwa [supportHausdorffGap_eq_hausdorffDist
      (hKcompact omega theta) (hLcompact omega theta)
      (hKne omega theta) (hLne omega theta)
      (hKconv omega theta) (hLconv omega theta)]
  calc
    mu {omega | ∃ theta,
        r < hausdorffDist (K omega theta) (L omega theta)} ≤
        mu (⋃ theta, A theta) := measure_mono hsub
    _ ≤ ∑' theta, mu (A theta) := measure_iUnion_le A
    _ ≤ ∑' theta, delta theta := ENNReal.tsum_le_tsum htail

end RandomSetTheory
