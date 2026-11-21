/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.SupportFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compact convex geometry and Hausdorff distance

This file establishes the support-function/Hausdorff bridge used throughout
random-set limit theory.  All real-valued Hausdorff statements explicitly
assume compact nonempty sets; mathlib's `hausdorffDist` has special behaviour
on the empty set.
-/

open Set Metric
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- Distance to a fixed point is 1-Lipschitz with respect to Hausdorff
distance on sets at finite Hausdorff distance.
@isnad1 id=le.1h4v.s5.7bc370199748 from=translated src=- shape=e6b41e4d vocab=47c56665
-/
theorem abs_infDist_sub_infDist_le_hausdorffDist
    {X : Type*} [PseudoMetricSpace X] (x : X) (s t : Set X)
    (hfin : hausdorffEDist s t ≠ ⊤) :
    |infDist x s - infDist x t| ≤ hausdorffDist s t := by
  rw [abs_sub_le_iff]
  have hst := infDist_le_infDist_add_hausdorffDist (x := x) hfin
  have hfin' : hausdorffEDist t s ≠ ⊤ := by
    simpa [hausdorffEDist_comm] using hfin
  have hts := infDist_le_infDist_add_hausdorffDist (x := x) hfin'
  rw [hausdorffDist_comm] at hts
  constructor <;> linarith

/-- In a normed space, the minimum-norm criterion (distance from zero) is
stable under Hausdorff perturbations.
@isnad1 id=le.1h3v.s6.ccf940a1502d from=translated src=- shape=dc5f3b1e vocab=d363c82a
-/
theorem abs_infDist_zero_sub_infDist_zero_le_hausdorffDist
    {X : Type*} [SeminormedAddCommGroup X] (s t : Set X)
    (hfin : hausdorffEDist s t ≠ ⊤) :
    |infDist 0 s - infDist 0 t| ≤ hausdorffDist s t :=
  abs_infDist_sub_infDist_le_hausdorffDist 0 s t hfin

/--
@isnad1 id=iscompac.1h2v.s7.d72c27da20d8 from=translated src=- shape=a750a729 vocab=032edfcb
-/
theorem closedConvexHull_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) :
    IsCompact (closedConvexHull ℝ K) := by
  rw [closedConvexHull_eq_closure_convexHull]
  exact (isBounded_convexHull.mpr hK.isBounded).isCompact_closure

/--
@isnad1 id=eq.2h3v.s7.8e8517449b2e from=translated src=- shape=808cd3bf vocab=cd1e4ae8
-/
theorem supportFunction_closedConvexHull {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty) (u : E) :
    supportFunction (closedConvexHull ℝ K) u = supportFunction K u := by
  have hc : IsCompact (closedConvexHull ℝ K) := closedConvexHull_compact hK
  have hinner : Continuous (fun y : E => ⟪u, y⟫_ℝ) := by fun_prop
  apply le_antisymm
  · obtain ⟨x, hx, hsup⟩ := supportFunction_attains hc
      (hKne.mono subset_closedConvexHull) u
    rw [hsup]
    have hsub : K ⊆ {y | ⟪u, y⟫_ℝ ≤ supportFunction K u} :=
      fun y hy => inner_le_supportFunction hK hy u
    exact closedConvexHull_min hsub
      (by simpa only [innerₗ_apply_apply] using
        convex_halfSpace_le (innerₗ E u).isLinear (supportFunction K u))
      (isClosed_Iic.preimage hinner) hx
  · exact supportFunction_mono hK hc hKne subset_closedConvexHull u

/-- A compact nonempty convex set is the intersection of the closed
half-spaces determined by its support function.
@isnad1 id=iff.3h3v.s7.78db50dca3ea from=translated src=- shape=4e11e96a vocab=60eaed4f
-/
theorem mem_iff_inner_le_supportFunction {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K) (x : E) :
    x ∈ K ↔ ∀ u : E, ⟪u, x⟫_ℝ ≤ supportFunction K u := by
  constructor
  · intro hx u
    exact inner_le_supportFunction hK hx u
  · intro hx
    by_contra hxK
    obtain ⟨y, hy, hmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex hKne hK.isComplete hKconv x
    let u := x - y
    have hproj : ∀ z ∈ K, ⟪u, z - y⟫_ℝ ≤ 0 := by
      simpa [u] using
        (norm_eq_iInf_iff_real_inner_le_zero hKconv hy).mp hmin
    have hsupport_y : supportFunction K u = ⟪u, y⟫_ℝ := by
      apply le_antisymm
      · obtain ⟨z, hz, hatt⟩ := supportFunction_attains hK hKne u
        rw [hatt]
        have hzproj := hproj z hz
        rw [inner_sub_right] at hzproj
        linarith
      · exact inner_le_supportFunction hK hy u
    have hxy : x ≠ y := fun hxy => hxK (hxy ▸ hy)
    have hu : u ≠ 0 := sub_ne_zero.mpr hxy
    have hstrict : supportFunction K u < ⟪u, x⟫_ℝ := by
      rw [hsupport_y]
      have hpos : 0 < ⟪u, u⟫_ℝ := real_inner_self_pos.mpr hu
      rw [show u = x - y from rfl, inner_sub_right] at hpos
      linarith
    exact (not_lt_of_ge (hx u)) hstrict

/-- Compact nonempty convex sets with the same support function are equal.-/
theorem eq_of_supportFunction_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L)
    (h : ∀ u : E, supportFunction K u = supportFunction L u) :
    K = L := by
  ext x
  rw [mem_iff_inner_le_supportFunction hK hKne hKconv,
    mem_iff_inner_le_supportFunction hL hLne hLconv]
  simp_rw [h]

/-- Closed convexification commutes with empirical Minkowski averaging for
compact nonempty values.
@isnad1 id=eq.2h4v.s8.39d93a6a4247 from=translated src=- shape=98b259d8 vocab=664d8be3
-/
theorem closedConvexHull_minkowskiAverage {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty) :
    closedConvexHull ℝ (minkowskiAverage s K) =
      minkowskiAverage s (fun i => closedConvexHull ℝ (K i)) := by
  have hAvgCompact : IsCompact (minkowskiAverage s K) :=
    isCompact_minkowskiAverage s K hK
  have hAvgNe : (minkowskiAverage s K).Nonempty :=
    nonempty_minkowskiAverage s K hKne
  have hHullCompact : ∀ i ∈ s, IsCompact (closedConvexHull ℝ (K i)) :=
    fun i hi => closedConvexHull_compact (hK i hi)
  have hHullNe : ∀ i ∈ s, (closedConvexHull ℝ (K i)).Nonempty :=
    fun i hi => (hKne i hi).mono subset_closedConvexHull
  apply eq_of_supportFunction_eq
    (closedConvexHull_compact hAvgCompact)
    (isCompact_minkowskiAverage s _ hHullCompact)
    (hAvgNe.mono subset_closedConvexHull)
    (nonempty_minkowskiAverage s _ hHullNe)
    convex_closedConvexHull
    (convex_minkowskiAverage s _ (fun _ _ => convex_closedConvexHull))
  intro u
  rw [supportFunction_closedConvexHull hAvgCompact hAvgNe u]
  rw [supportFunction_minkowskiAverage s K hK hKne u]
  rw [supportFunction_minkowskiAverage s _ hHullCompact hHullNe u]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact (supportFunction_closedConvexHull (hK i hi) (hKne i hi) u).symm

/-- One-sided support-function stability under Hausdorff perturbations.
@isnad1 id=le.4h4v.s6.2fa500368764 from=translated src=- shape=442a1114 vocab=5abfe6a4
-/
theorem supportFunction_sub_le_norm_mul_hausdorffDist {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) (u : E) :
    supportFunction K u - supportFunction L u ≤ ‖u‖ * hausdorffDist K L := by
  obtain ⟨x, hx, hxsup⟩ := supportFunction_attains hK hKne u
  obtain ⟨y, hy, hxy⟩ := hL.exists_infDist_eq_dist hLne x
  have hdist : dist x y ≤ hausdorffDist K L := by
    rw [← hxy]
    exact infDist_le_hausdorffDist_of_mem hx
      (hausdorffEDist_ne_top_of_nonempty_of_bounded
        hKne hLne hK.isBounded hL.isBounded)
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
    _ ≤ ‖u‖ * hausdorffDist K L :=
      mul_le_mul_of_nonneg_left hdist (norm_nonneg _)

/-- Hausdorff distance controls the support functions in every direction.
@isnad1 id=le.4h4v.s6.3207f12d6d32 from=translated src=- shape=da076f1f vocab=13092942
-/
theorem abs_supportFunction_sub_le_hausdorffDist {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) (u : E) :
    |supportFunction K u - supportFunction L u| ≤ ‖u‖ * hausdorffDist K L := by
  rw [abs_sub_le_iff]
  constructor
  · exact supportFunction_sub_le_norm_mul_hausdorffDist hK hL hKne hLne u
  · rw [hausdorffDist_comm]
    exact supportFunction_sub_le_norm_mul_hausdorffDist hL hK hLne hKne u

private theorem exists_mem_dist_le_of_supportFunction_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    {r : ℝ} (hr : 0 ≤ r)
    (hsupport : ∀ u : E,
      supportFunction K u - supportFunction L u ≤ r * ‖u‖)
    {x : E} (hx : x ∈ K) :
    ∃ y ∈ L, dist x y ≤ r := by
  obtain ⟨y, hy, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hLne hL.isComplete hLconv x
  have hproj : ∀ z ∈ L, ⟪x - y, z - y⟫_ℝ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hLconv hy).mp hmin
  have hsupport_y :
      supportFunction L (x - y) = ⟪x - y, y⟫_ℝ := by
    apply le_antisymm
    · obtain ⟨z, hz, hatt⟩ := supportFunction_attains hL hLne (x - y)
      rw [hatt]
      have hzproj := hproj z hz
      rw [inner_sub_right] at hzproj
      linarith
    · exact inner_le_supportFunction hL hy (x - y)
  have hsupport_x :
      ⟪x - y, x⟫_ℝ ≤ supportFunction K (x - y) :=
    inner_le_supportFunction hK hx (x - y)
  have hsq : ‖x - y‖ * ‖x - y‖ ≤ r * ‖x - y‖ := by
    calc
      ‖x - y‖ * ‖x - y‖ = ⟪x - y, x - y⟫_ℝ :=
        (real_inner_self_eq_norm_mul_norm (x - y)).symm
      _ = ⟪x - y, x⟫_ℝ - ⟪x - y, y⟫_ℝ := inner_sub_right _ _ _
      _ ≤ supportFunction K (x - y) - supportFunction L (x - y) := by
        rw [hsupport_y]
        exact sub_le_sub_right hsupport_x _
      _ ≤ r * ‖x - y‖ := hsupport (x - y)
  have hnorm : ‖x - y‖ ≤ r := by
    by_cases hzero : ‖x - y‖ = 0
    · simpa [hzero] using hr
    · have hpos : 0 < ‖x - y‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      nlinarith
  exact ⟨y, hy, by simpa [dist_eq_norm] using hnorm⟩

/-- Two directed support inequalities control Hausdorff distance.
@isnad1 id=le.9h4v.s8.55bc79370096 from=translated src=- shape=2d69089c vocab=4d0df4d4
-/
theorem hausdorffDist_le_of_supportFunction_sub_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L)
    {r : ℝ} (hr : 0 ≤ r)
    (hKL : ∀ u : E,
      supportFunction K u - supportFunction L u ≤ r * ‖u‖)
    (hLK : ∀ u : E,
      supportFunction L u - supportFunction K u ≤ r * ‖u‖) :
    hausdorffDist K L ≤ r := by
  apply hausdorffDist_le_of_mem_dist hr
  · intro x hx
    exact exists_mem_dist_le_of_supportFunction_sub_le
      hK hL hLne hLconv hr hKL hx
  · intro y hy
    obtain ⟨x, hx, hdist⟩ := exists_mem_dist_le_of_supportFunction_sub_le
      hL hK hKne hKconv hr hLK hy
    exact ⟨x, hx, by simpa [dist_comm] using hdist⟩

/-- A uniform absolute support bound controls Hausdorff distance.
@isnad1 id=le.8h4v.s8.9f9447d1994b from=translated src=- shape=63141e5a vocab=845b6590
-/
theorem hausdorffDist_le_of_abs_supportFunction_sub_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L)
    {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ u : E,
      |supportFunction K u - supportFunction L u| ≤ r * ‖u‖) :
    hausdorffDist K L ≤ r := by
  apply hausdorffDist_le_of_supportFunction_sub_le hK hL hKne hLne
    hKconv hLconv hr
  · intro u
    exact (le_abs_self _).trans (h u)
  · intro u
    have hu := h u
    rw [abs_sub_comm] at hu
    exact (le_abs_self _).trans hu

/-- It is enough to control support functions on the closed unit ball.
@isnad1 id=le.8h4v.s8.50c47becf3a7 from=translated src=- shape=abf2990b vocab=4427e49b
-/
theorem hausdorffDist_le_of_unitBall_supportFunction_sub_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L)
    {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ u : E, ‖u‖ ≤ 1 →
      |supportFunction K u - supportFunction L u| ≤ r) :
    hausdorffDist K L ≤ r := by
  apply hausdorffDist_le_of_abs_supportFunction_sub_le
    hK hL hKne hLne hKconv hLconv hr
  intro u
  by_cases hu : u = 0
  · subst u
    simp [supportFunction_zero hK hKne, supportFunction_zero hL hLne]
  · let v : E := ‖u‖⁻¹ • u
    have hunorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hvnorm : ‖v‖ = 1 := by
      simp [v, norm_smul, hunorm]
    have huv : ‖u‖ • v = u := by
      simp [v, smul_smul, hunorm]
    have hKu : supportFunction K u = ‖u‖ * supportFunction K v := by
      calc
        supportFunction K u = supportFunction K (‖u‖ • v) := congrArg _ huv.symm
        _ = ‖u‖ * supportFunction K v :=
          supportFunction_smul_direction hK hKne (norm_nonneg u) v
    have hLu : supportFunction L u = ‖u‖ * supportFunction L v := by
      calc
        supportFunction L u = supportFunction L (‖u‖ • v) := congrArg _ huv.symm
        _ = ‖u‖ * supportFunction L v :=
          supportFunction_smul_direction hL hLne (norm_nonneg u) v
    rw [hKu, hLu, ← mul_sub, abs_mul, abs_of_nonneg (norm_nonneg u)]
    calc
      ‖u‖ * |supportFunction K v - supportFunction L v| ≤ ‖u‖ * r :=
        mul_le_mul_of_nonneg_left (h v hvnorm.le) (norm_nonneg u)
      _ = r * ‖u‖ := mul_comm _ _

/-- A finite `ε`-net of the unit ball reduces Hausdorff control to finitely
many support-function evaluations.
@isnad1 id=le.12h8v.s8.8df00d4abdc5 from=translated src=- shape=a53db1ac vocab=006766cb
-/
theorem hausdorffDist_le_of_finset_net_supportFunction {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L)
    {RK RL eps s : ℝ}
    (hRK : ∀ x ∈ K, ‖x‖ ≤ RK) (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (hs : 0 ≤ s)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (hN : ∀ v ∈ N,
      |supportFunction K v - supportFunction L v| ≤ s) :
    hausdorffDist K L ≤ s + (RK + RL) * eps := by
  have hRK0 : 0 ≤ RK := by
    obtain ⟨x, hx⟩ := hKne
    exact (norm_nonneg x).trans (hRK x hx)
  have hRL0 : 0 ≤ RL := by
    obtain ⟨x, hx⟩ := hLne
    exact (norm_nonneg x).trans (hRL x hx)
  apply hausdorffDist_le_of_unitBall_supportFunction_sub_le
    hK hL hKne hLne hKconv hLconv
    (add_nonneg hs (mul_nonneg (add_nonneg hRK0 hRL0) heps))
  intro u hu
  obtain ⟨v, hvN, huv⟩ := hnet u hu
  have hLip := abs_supportFunctionDifference_sub_le
    hK hL hKne hLne hRK hRL u v
  have hdistnorm : ‖u - v‖ = dist u v := by rw [dist_eq_norm]
  calc
    |supportFunction K u - supportFunction L u| =
        |(supportFunction K v - supportFunction L v) +
          ((supportFunction K u - supportFunction L u) -
            (supportFunction K v - supportFunction L v))| := by
              congr 1
              ring
    _ ≤ |supportFunction K v - supportFunction L v| +
        |(supportFunction K u - supportFunction L u) -
          (supportFunction K v - supportFunction L v)| := abs_add_le _ _
    _ ≤ s + (RK + RL) * ‖u - v‖ := add_le_add (hN v hvN) hLip
    _ = s + (RK + RL) * dist u v := by rw [hdistnorm]
    _ ≤ s + (RK + RL) * eps := by
      gcongr

/-- Supremum norm of the difference of support functions on the unit ball.-/
def supportHausdorffGap {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K L : Set E) : ℝ :=
  sSup ((fun u : E => |supportFunction K u - supportFunction L u|) ''
    Metric.closedBall 0 1)

/-- For compact nonempty convex sets, Hausdorff distance is exactly the
uniform distance of support functions on the unit ball.
@isnad1 id=eq.6h3v.s7.fa9fcbcf2d7f from=translated src=- shape=d366f3cc vocab=d0086c72
-/
theorem supportHausdorffGap_eq_hausdorffDist {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) :
    supportHausdorffGap K L = hausdorffDist K L := by
  let A : Set ℝ :=
    (fun u : E => |supportFunction K u - supportFunction L u|) ''
      Metric.closedBall 0 1
  have hupper : ∀ z ∈ A, z ≤ hausdorffDist K L := by
    rintro z ⟨u, hu, rfl⟩
    have hunorm : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hu
    calc
      |supportFunction K u - supportFunction L u| ≤
          ‖u‖ * hausdorffDist K L :=
        abs_supportFunction_sub_le_hausdorffDist hK hL hKne hLne u
      _ ≤ 1 * hausdorffDist K L :=
        mul_le_mul_of_nonneg_right hunorm hausdorffDist_nonneg
      _ = hausdorffDist K L := one_mul _
  have hAne : A.Nonempty := by
    refine ⟨|supportFunction K 0 - supportFunction L 0|, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hAbdd : BddAbove A := ⟨hausdorffDist K L, hupper⟩
  apply le_antisymm
  · change sSup A ≤ hausdorffDist K L
    exact csSup_le hAne hupper
  · apply hausdorffDist_le_of_unitBall_supportFunction_sub_le
      hK hL hKne hLne hKconv hLconv
    · change 0 ≤ sSup A
      have hzero : (0 : ℝ) ∈ A := by
        refine ⟨0, by simp, ?_⟩
        simp [supportFunction_zero hK hKne, supportFunction_zero hL hLne]
      exact le_csSup hAbdd hzero
    · intro u hu
      change |supportFunction K u - supportFunction L u| ≤ sSup A
      apply le_csSup hAbdd
      exact ⟨u, by simpa [Metric.mem_closedBall] using hu, rfl⟩

/-- Closed convexification is nonexpansive for Hausdorff distance.
@isnad1 id=le.4h3v.s7.215366f8b4bd from=translated src=- shape=bc465d5a vocab=31f057a8
-/
theorem hausdorffDist_closedConvexHull_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set E} (hs : IsCompact s) (ht : IsCompact t)
    (sne : s.Nonempty) (tne : t.Nonempty) :
    hausdorffDist (closedConvexHull ℝ s) (closedConvexHull ℝ t) ≤
      hausdorffDist s t := by
  let r := hausdorffDist s t
  have hfin : hausdorffEDist s t ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded sne tne hs.isBounded ht.isBounded
  have hst : s ⊆ cthickening r (closedConvexHull ℝ t) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := ht.exists_infDist_eq_dist tne x
    apply mem_cthickening_of_dist_le x y r (closedConvexHull ℝ t)
    · exact subset_closedConvexHull hy
    · rw [← hxy]
      exact infDist_le_hausdorffDist_of_mem hx hfin
  have hts : t ⊆ cthickening r (closedConvexHull ℝ s) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := hs.exists_infDist_eq_dist sne y
    apply mem_cthickening_of_dist_le y x r (closedConvexHull ℝ s)
    · exact subset_closedConvexHull hx
    · rw [← hyx]
      change infDist y s ≤ hausdorffDist s t
      rw [hausdorffDist_comm]
      apply infDist_le_hausdorffDist_of_mem hy
      rwa [hausdorffEDist_comm]
  have hcst : closedConvexHull ℝ s ⊆ cthickening r (closedConvexHull ℝ t) :=
    closedConvexHull_min hst (convex_closedConvexHull.cthickening r)
      isClosed_cthickening
  have hcts : closedConvexHull ℝ t ⊆ cthickening r (closedConvexHull ℝ s) :=
    closedConvexHull_min hts (convex_closedConvexHull.cthickening r)
      isClosed_cthickening
  apply hausdorffDist_le_of_infDist hausdorffDist_nonneg
  · intro x hx
    exact calc
      infDist x (closedConvexHull ℝ t) =
          (infEDist x (closedConvexHull ℝ t)).toReal := rfl
      _ ≤ (ENNReal.ofReal r).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcst hx)
      _ = r := ENNReal.toReal_ofReal hausdorffDist_nonneg
  · intro y hy
    exact calc
      infDist y (closedConvexHull ℝ s) =
          (infEDist y (closedConvexHull ℝ s)).toReal := rfl
      _ ≤ (ENNReal.ofReal r).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcts hy)
      _ = r := ENNReal.toReal_ofReal hausdorffDist_nonneg

/-- A Lipschitz map contracts Hausdorff distance up to its Lipschitz
constant.  Compactness and nonemptiness make the real Hausdorff distances
finite and provide nearest points in both directions.
@isnad1 id=le.5h6v.s6.7cd1f8e49c23 from=translated src=- shape=c64c597d vocab=d42423a4
-/
theorem hausdorffDist_image_le_of_lipschitzWith
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K L : Set X} {c : NNReal}
    (hf : LipschitzWith c f) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    hausdorffDist (f '' K) (f '' L) ≤
      (c : ℝ) * hausdorffDist K L := by
  have hfin : hausdorffEDist K L ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded
      hKne hLne hK.isBounded hL.isBounded
  apply hausdorffDist_le_of_mem_dist
    (mul_nonneg c.coe_nonneg hausdorffDist_nonneg)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hL.exists_infDist_eq_dist hLne x
    refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩
    calc
      dist (f x) (f y) ≤ (c : ℝ) * dist x y := hf.dist_le_mul x y
      _ = (c : ℝ) * infDist x L := by rw [hxy]
      _ ≤ (c : ℝ) * hausdorffDist K L := by
        gcongr
        exact infDist_le_hausdorffDist_of_mem hx hfin
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := hK.exists_infDist_eq_dist hKne y
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    calc
      dist (f y) (f x) ≤ (c : ℝ) * dist y x := hf.dist_le_mul y x
      _ = (c : ℝ) * infDist y K := by rw [hyx]
      _ ≤ (c : ℝ) * hausdorffDist K L := by
        gcongr
        rw [hausdorffDist_comm]
        apply infDist_le_hausdorffDist_of_mem hy
        simpa [hausdorffEDist_comm] using hfin

/-- To control the nonconvexity of a set, it is enough to approximate every
point of its closed convex hull by a point of the original set.
@isnad1 id=le.2h3v.s7.551ceac0ae55 from=translated src=- shape=bb328b90 vocab=b2b9189f
-/
theorem hausdorffDist_self_closedConvexHull_le_of_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {r : ℝ} (hr : 0 ≤ r)
    (happrox : ∀ x ∈ closedConvexHull ℝ s, ∃ y ∈ s, dist x y ≤ r) :
    hausdorffDist s (closedConvexHull ℝ s) ≤ r := by
  apply hausdorffDist_le_of_mem_dist hr
  · intro x hx
    exact ⟨x, subset_closedConvexHull hx, by simpa using hr⟩
  · exact happrox

end RandomSetTheory
