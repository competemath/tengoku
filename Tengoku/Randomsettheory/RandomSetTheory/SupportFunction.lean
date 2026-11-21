/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real support functions of compact sets

For the compact nonempty random sets used in random-set theory, support
functions are finite and naturally real-valued.  Keeping the codomain `ℝ`
avoids the indeterminate products `0 * ⊤` and `0 * ⊥` that arise when convex
combinations are performed in `EReal`.

The file proves the classical algebraic and analytic facts needed by Aumann
expectations and empirical Minkowski averages: attainment, positive
homogeneity, sublinearity, invariance under convexification, Minkowski
additivity, finite-sum formulas, and Lipschitz control in the direction.
-/

open Set
open scoped InnerProductSpace Pointwise BigOperators

noncomputable section

namespace RandomSetTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `σ_K(u) = sup {⟪u,x⟫ | x ∈ K}`.  The useful API below assumes that `K`
is compact and nonempty, which is exactly when this real supremum is finite
and attained.-/
def supportFunction (K : Set E) (u : E) : ℝ :=
  sSup ((fun x => ⟪u, x⟫_ℝ) '' K)

/--
@isnad1 id=le.2h4v.s6.3f5808d6f30e from=translated src=- shape=68944d8b vocab=4cdac587
-/
theorem inner_le_supportFunction {K : Set E} (hK : IsCompact K)
    {x : E} (hx : x ∈ K) (u : E) :
    ⟪u, x⟫_ℝ ≤ supportFunction K u := by
  apply le_csSup
  · exact (hK.image (by fun_prop)).bddAbove
  · exact ⟨x, hx, rfl⟩

/--
@isnad1 id=ex.2h3v.s6.247d41d10c22 from=translated src=- shape=adbd55a8 vocab=7c335975
-/
theorem supportFunction_attains {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) (u : E) :
    ∃ x ∈ K, supportFunction K u = ⟪u, x⟫_ℝ := by
  obtain ⟨x, hx, hxmax⟩ :=
    hK.exists_isMaxOn hKne
      (by fun_prop : ContinuousOn (fun x : E => ⟪u, x⟫_ℝ) K)
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · apply csSup_le
    · exact ⟨⟪u, x⟫_ℝ, x, hx, rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      exact hxmax hz
  · exact inner_le_supportFunction hK hx u

/--
@isnad1 id=eq.0h3v.s5.440c45f72477 from=translated src=- shape=b0db6e3f vocab=9f5f010f
-/
@[simp]
theorem supportFunction_singleton (x u : E) :
    supportFunction ({x} : Set E) u = ⟪u, x⟫_ℝ := by
  simp [supportFunction]

/--
@isnad1 id=eq.2h2v.s6.684c616e3973 from=translated src=- shape=3a898f54 vocab=64ff2641
-/
@[simp]
theorem supportFunction_zero {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) : supportFunction K 0 = 0 := by
  obtain ⟨x, _hx, hmax⟩ := supportFunction_attains hK hKne 0
  simpa using hmax

/-- Positive homogeneity in the direction.
@isnad1 id=eq.3h4v.s7.9f687f9c9579 from=translated src=- shape=95fa6f0d vocab=6b535b0a
-/
theorem supportFunction_smul_direction {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) {c : ℝ} (hc : 0 ≤ c) (u : E) :
    supportFunction K (c • u) = c * supportFunction K u := by
  obtain ⟨x, hx, hxmax⟩ := supportFunction_attains hK hKne (c • u)
  obtain ⟨y, hy, hymax⟩ := supportFunction_attains hK hKne u
  apply le_antisymm
  · rw [hxmax, real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (inner_le_supportFunction hK hx u) hc
  · rw [hymax, ← real_inner_smul_left]
    exact inner_le_supportFunction hK hy (c • u)

/-- Subadditivity in the direction.
@isnad1 id=le.2h4v.s6.293559b6cc4f from=translated src=- shape=3d463f9b vocab=1460c8d2
-/
theorem supportFunction_add_direction_le {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) (u v : E) :
    supportFunction K (u + v) ≤ supportFunction K u + supportFunction K v := by
  obtain ⟨x, hx, hmax⟩ := supportFunction_attains hK hKne (u + v)
  rw [hmax, inner_add_left]
  exact add_le_add (inner_le_supportFunction hK hx u)
    (inner_le_supportFunction hK hx v)

/-- A support function is convex on the whole ambient space.
@isnad1 id=convexon.2h2v.s6.b4f97e865a3e from=translated src=- shape=e4be114c vocab=cd0a3299
-/
theorem supportFunction_convexOn {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) :
    ConvexOn ℝ Set.univ (supportFunction K) := by
  refine ⟨convex_univ, ?_⟩
  intro u _hu v _hv a b ha hb hab
  obtain ⟨x, hx, hmax⟩ :=
    supportFunction_attains hK hKne (a • u + b • v)
  rw [hmax, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc
    a * ⟪u, x⟫_ℝ + b * ⟪v, x⟫_ℝ ≤
        a * supportFunction K u + b * supportFunction K v :=
      add_le_add
        (mul_le_mul_of_nonneg_left (inner_le_supportFunction hK hx u) ha)
        (mul_le_mul_of_nonneg_left (inner_le_supportFunction hK hx v) hb)
    _ = a • supportFunction K u + b • supportFunction K v := by
      simp [smul_eq_mul]

/-- Monotonicity under inclusion, for compact sets.
@isnad1 id=le.4h4v.s6.f9cc4949815c from=translated src=- shape=5996f8b1 vocab=0abd0a34
-/
theorem supportFunction_mono {K L : Set E} (hK : IsCompact K)
    (hL : IsCompact L) (hKne : K.Nonempty) (hKL : K ⊆ L) (u : E) :
    supportFunction K u ≤ supportFunction L u := by
  obtain ⟨x, hx, hmax⟩ := supportFunction_attains hK hKne u
  rw [hmax]
  exact inner_le_supportFunction hL (hKL hx) u

/-- Taking the topological closure does not change the support function as
soon as that closure is compact and the original set is nonempty.

Unlike the compact-set monotonicity lemma, this result deliberately does not
assume that `K` itself is closed.  It is useful for raw Aumann expectations:
their closure is compact under an integrable envelope even when closedness of
the unclosed expectation has not yet been established.
@isnad1 id=eq.2h3v.s6.4b96e9e008f1 from=translated src=- shape=12341968 vocab=10508ba2
-/
theorem supportFunction_closure_eq {K : Set E}
    (hKcompact : IsCompact (closure K)) (hKne : K.Nonempty) (u : E) :
    supportFunction (closure K) u = supportFunction K u := by
  have hclosureNe : (closure K).Nonempty := hKne.closure
  have hbounded : BddAbove ((fun x : E ↦ ⟪u, x⟫_ℝ) '' K) := by
    refine ⟨supportFunction (closure K) u, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact inner_le_supportFunction hKcompact (subset_closure hx) u
  apply le_antisymm
  · obtain ⟨x, hx, hmax⟩ :=
      supportFunction_attains hKcompact hclosureNe u
    rw [hmax]
    apply closure_minimal (s := K)
        (t := {y : E | ⟪u, y⟫_ℝ ≤ supportFunction K u}) ?_ ?_ hx
    · intro y hy
      exact le_csSup hbounded ⟨y, hy, rfl⟩
    · exact isClosed_le (by fun_prop : Continuous fun y : E ↦ ⟪u, y⟫_ℝ)
        continuous_const
  · apply csSup_le
    · obtain ⟨x, hx⟩ := hKne
      exact ⟨⟪u, x⟫_ℝ, x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact inner_le_supportFunction hKcompact (subset_closure hx) u

/-- Convexification does not change the support function.
@isnad1 id=eq.2h3v.s6.24e49e119601 from=translated src=- shape=f442dddb vocab=6993d943
-/
theorem supportFunction_convexHull {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) (u : E) :
    supportFunction (convexHull ℝ K) u = supportFunction K u := by
  have hKle : K ⊆ {x : E | ⟪u, x⟫_ℝ ≤ supportFunction K u} :=
    fun _ hx => inner_le_supportFunction hK hx u
  have hhalf : Convex ℝ {x : E | ⟪u, x⟫_ℝ ≤ supportFunction K u} :=
    convex_halfSpace_le (innerSL ℝ u).toLinearMap.isLinear _
  have hhull : convexHull ℝ K ⊆
      {x : E | ⟪u, x⟫_ℝ ≤ supportFunction K u} :=
    convexHull_min hKle hhalf
  apply le_antisymm
  · apply csSup_le
    · obtain ⟨x, hx⟩ := hKne
      exact ⟨⟪u, x⟫_ℝ, x, subset_convexHull ℝ K hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hhull hx
  · obtain ⟨x, hx, hmax⟩ := supportFunction_attains hK hKne u
    rw [hmax]
    apply le_csSup
    · exact ⟨supportFunction K u, by
        rintro _ ⟨y, hy, rfl⟩
        exact hhull hy⟩
    · exact ⟨x, subset_convexHull ℝ K hx, rfl⟩

/-- The support function transforms a Minkowski sum into a real sum.
@isnad1 id=eq.4h4v.s6.0792e7956ced from=translated src=- shape=b0cdded5 vocab=00cde54a
-/
theorem supportFunction_add {K L : Set E} (hK : IsCompact K)
    (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty) (u : E) :
    supportFunction (K + L) u = supportFunction K u + supportFunction L u := by
  have hKL : IsCompact (K + L) := hK.add hL
  have hKLne : (K + L).Nonempty := hKne.add hLne
  obtain ⟨z, hz, hzmax⟩ := supportFunction_attains hKL hKLne u
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
  rw [hzmax, inner_add_right]
  apply le_antisymm
  · exact add_le_add (inner_le_supportFunction hK hx u)
      (inner_le_supportFunction hL hy u)
  · obtain ⟨x', hx', hx'max⟩ := supportFunction_attains hK hKne u
    obtain ⟨y', hy', hy'max⟩ := supportFunction_attains hL hLne u
    calc
      supportFunction K u + supportFunction L u =
          ⟪u, x'⟫_ℝ + ⟪u, y'⟫_ℝ := by rw [hx'max, hy'max]
      _ = ⟪u, x' + y'⟫_ℝ := (inner_add_right u x' y').symm
      _ ≤ supportFunction (K + L) u :=
        inner_le_supportFunction hKL (Set.add_mem_add hx' hy') u
      _ = ⟪u, x⟫_ℝ + ⟪u, y⟫_ℝ := by rw [hzmax, inner_add_right]

/-- A nonnegative dilation of a set dilates its support function.
@isnad1 id=eq.3h4v.s7.675f34b192bb from=translated src=- shape=a97447f7 vocab=1ba1e4de
-/
theorem supportFunction_smul_set {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) {c : ℝ} (hc : 0 ≤ c) (u : E) :
    supportFunction (c • K) u = c * supportFunction K u := by
  have hcK : IsCompact (c • K) := hK.smul c
  have hcKne : (c • K).Nonempty := hKne.smul_set
  obtain ⟨z, hz, hzmax⟩ := supportFunction_attains hcK hcKne u
  obtain ⟨x, hx, hcx⟩ := Set.mem_smul_set.mp hz
  obtain ⟨y, hy, hymax⟩ := supportFunction_attains hK hKne u
  apply le_antisymm
  · rw [hzmax, ← hcx, real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (inner_le_supportFunction hK hx u) hc
  · rw [hymax, ← real_inner_smul_right]
    exact inner_le_supportFunction hcK (Set.smul_mem_smul_set hy) u

/-- Uniform radius control makes the support function Lipschitz in its
direction.
@isnad1 id=le.3h5v.s6.5a82bfb28460 from=translated src=- shape=056b02bd vocab=ae53f7a3
-/
theorem abs_supportFunction_sub_le {K : Set E} (hK : IsCompact K)
    (hKne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u v : E) :
    |supportFunction K u - supportFunction K v| ≤ R * ‖u - v‖ := by
  obtain ⟨x, hx, hxmax⟩ := supportFunction_attains hK hKne u
  obtain ⟨y, hy, hymax⟩ := supportFunction_attains hK hKne v
  rw [abs_sub_le_iff]
  constructor
  · calc
      supportFunction K u - supportFunction K v =
          ⟪u, x⟫_ℝ - supportFunction K v := by rw [hxmax]
      _ ≤ ⟪u, x⟫_ℝ - ⟪v, x⟫_ℝ := by
        gcongr
        exact inner_le_supportFunction hK hx v
      _ = ⟪u - v, x⟫_ℝ := (inner_sub_left _ _ _).symm
      _ ≤ |⟪u - v, x⟫_ℝ| := le_abs_self _
      _ ≤ ‖u - v‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖u - v‖ * R :=
        mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _)
      _ = R * ‖u - v‖ := mul_comm _ _
  · calc
      supportFunction K v - supportFunction K u =
          ⟪v, y⟫_ℝ - supportFunction K u := by rw [hymax]
      _ ≤ ⟪v, y⟫_ℝ - ⟪u, y⟫_ℝ := by
        gcongr
        exact inner_le_supportFunction hK hy u
      _ = ⟪v - u, y⟫_ℝ := (inner_sub_left _ _ _).symm
      _ ≤ |⟪v - u, y⟫_ℝ| := le_abs_self _
      _ ≤ ‖v - u‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v - u‖ * R :=
        mul_le_mul_of_nonneg_left (hR y hy) (norm_nonneg _)
      _ = R * ‖u - v‖ := by rw [norm_sub_rev, mul_comm]

/-- The difference of two support functions is Lipschitz with constant the
sum of radii containing the two sets.
@isnad1 id=le.6h7v.s7.8a6b740fc35d from=translated src=- shape=9bb6428e vocab=ec88c8d3
-/
theorem abs_supportFunctionDifference_sub_le {K L : Set E}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) {RK RL : ℝ}
    (hRK : ∀ x ∈ K, ‖x‖ ≤ RK) (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (u v : E) :
    |(supportFunction K u - supportFunction L u) -
        (supportFunction K v - supportFunction L v)| ≤
      (RK + RL) * ‖u - v‖ := by
  have hKu := abs_supportFunction_sub_le hK hKne hRK u v
  have hLu := abs_supportFunction_sub_le hL hLne hRL u v
  calc
    |(supportFunction K u - supportFunction L u) -
        (supportFunction K v - supportFunction L v)| =
        |(supportFunction K u - supportFunction K v) +
          -(supportFunction L u - supportFunction L v)| := by
            congr 1
            ring
    _ ≤ |supportFunction K u - supportFunction K v| +
        |-(supportFunction L u - supportFunction L v)| := abs_add_le _ _
    _ = |supportFunction K u - supportFunction K v| +
        |supportFunction L u - supportFunction L v| := by rw [abs_neg]
    _ ≤ RK * ‖u - v‖ + RL * ‖u - v‖ := add_le_add hKu hLu
    _ = (RK + RL) * ‖u - v‖ := by ring

omit [InnerProductSpace ℝ E] in
/--
@isnad1 id=iscompac.1h4v.s6.e7ec959bd6c3 from=translated src=- shape=effb8213 vocab=8c8e90d1
-/
theorem isCompact_finset_sum {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) : IsCompact (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hK a (Finset.mem_insert_self a s)).add <|
        ih fun i hi => hK i (Finset.mem_insert_of_mem hi)

omit [InnerProductSpace ℝ E] in
/--
@isnad1 id=nonempty.1h4v.s5.4039c5215b00 from=translated src=- shape=effb8213 vocab=471c48be
-/
theorem nonempty_finset_sum {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hKne : ∀ i ∈ s, (K i).Nonempty) : (∑ i ∈ s, K i).Nonempty := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hKne a (Finset.mem_insert_self a s)).add <|
        ih fun i hi => hKne i (Finset.mem_insert_of_mem hi)

omit [InnerProductSpace ℝ E] in
/-- A point in a finite Minkowski sum is bounded by the sum of any
pointwise radius bounds.
@isnad1 id=le.2h6v.s6.96360c72f178 from=translated src=- shape=f6dbbb94 vocab=9c02ec87
-/
theorem norm_le_sum_radius_of_mem_finset_sum
    {ι : Type*} (s : Finset ι) (K : ι → Set E) (R : ι → ℝ)
    (hR : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R i)
    {x : E} (hx : x ∈ ∑ i ∈ s, K i) :
    ‖x‖ ≤ ∑ i ∈ s, R i := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
      simp only [Finset.sum_empty] at hx ⊢
      subst x
      exact norm_zero.le
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at hx ⊢
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
      calc
        ‖y + z‖ ≤ ‖y‖ + ‖z‖ := norm_add_le _ _
        _ ≤ R a + ∑ i ∈ s, R i := add_le_add
          (hR a (Finset.mem_insert_self a s) y hy)
          (ih (fun i hi => hR i (Finset.mem_insert_of_mem hi)) hz)

/-- Formula for a finite Minkowski sum.
@isnad1 id=eq.2h5v.s6.bbc4684de82f from=translated src=- shape=76b5bd04 vocab=9f04f15f
-/
theorem supportFunction_finset_sum {ι : Type*} (s : Finset ι)
    (K : ι → Set E) (hK : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty) (u : E) :
    supportFunction (∑ i ∈ s, K i) u =
      ∑ i ∈ s, supportFunction (K i) u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change supportFunction ({0} : Set E) u = 0
      simp
  | @insert a s ha ih =>
      have hKa : IsCompact (K a) := hK a (Finset.mem_insert_self a s)
      have hKane : (K a).Nonempty := hKne a (Finset.mem_insert_self a s)
      have hKs : ∀ i ∈ s, IsCompact (K i) :=
        fun i hi => hK i (Finset.mem_insert_of_mem hi)
      have hKsne : ∀ i ∈ s, (K i).Nonempty :=
        fun i hi => hKne i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [supportFunction_add hKa (isCompact_finset_sum s K hKs)
        hKane (nonempty_finset_sum s K hKsne) u]
      rw [ih hKs hKsne]

/--
@isnad1 id=eq.2h4v.s6.9e81a3c3f886 from=translated src=- shape=d82fbc43 vocab=a55ca226
-/
theorem supportFunction_univ_sum {ι : Type*} [Fintype ι] (K : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hKne : ∀ i, (K i).Nonempty) (u : E) :
    supportFunction (∑ i, K i) u = ∑ i, supportFunction (K i) u :=
  supportFunction_finset_sum Finset.univ K
    (fun i _ => hK i) (fun i _ => hKne i) u

/-- The empirical Minkowski average over a finite index set.-/
def minkowskiAverage {ι : Type*} (s : Finset ι) (K : ι → Set E) : Set E :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, K i

/-- Radius bound for an empirical Minkowski average.
@isnad1 id=le.2h6v.s6.e5fdd3cc2a9a from=translated src=- shape=fe1172e2 vocab=d111d2b8
-/
theorem norm_le_average_radius_of_mem_minkowskiAverage
    {ι : Type*} (s : Finset ι) (K : ι → Set E) (R : ι → ℝ)
    (hR : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R i)
    {x : E} (hx : x ∈ minkowskiAverage s K) :
    ‖x‖ ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, R i := by
  rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg s.card))]
  exact mul_le_mul_of_nonneg_left
    (norm_le_sum_radius_of_mem_finset_sum s K R hR hy)
    (inv_nonneg.mpr (Nat.cast_nonneg s.card))

/-- Convexification commutes with a finite Minkowski sum.
@isnad1 id=eq.0h4v.s7.2b58b2e6019f from=translated src=- shape=c5294248 vocab=f3c60052
-/
theorem convexHull_finset_sum {ι : Type*} (s : Finset ι) (K : ι → Set E) :
    convexHull ℝ (∑ i ∈ s, K i) = ∑ i ∈ s, convexHull ℝ (K i) := by
  exact convexHull_sum s K

/-- Empirical convexification identity used for random-set averages:
`conv (n⁻¹ • ∑ Kᵢ) = n⁻¹ • ∑ conv Kᵢ`.
@isnad1 id=eq.0h4v.s7.ec859ff9ab75 from=translated src=- shape=709a638e vocab=9ae48dda
-/
theorem convexHull_minkowskiAverage {ι : Type*} (s : Finset ι) (K : ι → Set E) :
    convexHull ℝ (minkowskiAverage s K) =
      minkowskiAverage s (fun i => convexHull ℝ (K i)) := by
  unfold minkowskiAverage
  rw [convexHull_smul, convexHull_sum]

/--
@isnad1 id=iscompac.1h4v.s6.e27c398858e7 from=translated src=- shape=9d4b2b0a vocab=2e8e3d85
-/
theorem isCompact_minkowskiAverage {ι : Type*} (s : Finset ι)
    (K : ι → Set E) (hK : ∀ i ∈ s, IsCompact (K i)) :
    IsCompact (minkowskiAverage s K) :=
  (isCompact_finset_sum s K hK).smul (s.card : ℝ)⁻¹

/--
@isnad1 id=nonempty.1h4v.s5.ff159ebf662f from=translated src=- shape=9d4b2b0a vocab=1475b72c
-/
theorem nonempty_minkowskiAverage {ι : Type*} (s : Finset ι)
    (K : ι → Set E) (hKne : ∀ i ∈ s, (K i).Nonempty) :
    (minkowskiAverage s K).Nonempty :=
  (nonempty_finset_sum s K hKne).smul_set

/--
@isnad1 id=convex.1h4v.s7.3f432341c37e from=translated src=- shape=43db0062 vocab=4ddeefb2
-/
theorem convex_minkowskiAverage {ι : Type*} (s : Finset ι)
    (K : ι → Set E) (hKconv : ∀ i ∈ s, Convex ℝ (K i)) :
    Convex ℝ (minkowskiAverage s K) :=
  (convex_sum K hKconv).smul (s.card : ℝ)⁻¹

/-- Support functions turn an empirical Minkowski average into the ordinary
arithmetic average of support functions.
@isnad1 id=eq.2h5v.s6.064e08adf093 from=translated src=- shape=8fb8321c vocab=62838ed1
-/
theorem supportFunction_minkowskiAverage {ι : Type*} (s : Finset ι)
    (K : ι → Set E) (hK : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty) (u : E) :
    supportFunction (minkowskiAverage s K) u =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, supportFunction (K i) u := by
  classical
  unfold minkowskiAverage
  rw [supportFunction_smul_set (isCompact_finset_sum s K hK)
    (nonempty_finset_sum s K hKne) (inv_nonneg.mpr (Nat.cast_nonneg s.card))]
  rw [supportFunction_finset_sum s K hK hKne]

end RandomSetTheory
