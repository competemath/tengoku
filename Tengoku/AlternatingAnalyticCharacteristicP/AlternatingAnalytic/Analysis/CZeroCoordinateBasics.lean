import Tengoku.Seed.Topology.ContinuousMap.ZeroAtInfty
import Tengoku.Seed.Analysis.Normed.Operator.Basic
import Tengoku.Seed.Topology.Order.MonotoneConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinates and finite truncations in `C₀(I, K)`

Coordinate vectors, coordinate evaluations and finite truncations on `C₀(I, K)` for a
discrete index type `I`, with the sup norm. Truncations converge to every vector, so
finitely supported vectors are dense.
-/

noncomputable section

open scoped Topology ZeroAtInfty
open Filter

namespace CZero

universe u v
variable {I : Type u} {K : Type v} [TopologicalSpace I] [DiscreteTopology I]
  [NontriviallyNormedField K]

local instance : DecidableEq I := Classical.decEq I

/-- Regard a finitely supported function on a discrete space as an element of `C₀`.-/
def ofFiniteSupport (f : I → K) (hf : f.HasFiniteSupport) : C₀(I, K) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite]
    exact (tendsto_cofinite_pure_iff.mpr hf).mono_right (pure_le_nhds _)

/--
@isnad1 id=eq.1h4v.s6.254bc6dd12e1 from=translated src=- shape=654e6fc7 vocab=2f95ae32
-/
@[simp] theorem ofFiniteSupport_apply (f : I → K) (hf : f.HasFiniteSupport) (i : I) :
    ofFiniteSupport f hf i = f i := rfl

/-- The coordinate vector supported at `i`, with value one there.-/
def coordinate (i : I) : C₀(I, K) := by
  classical
  exact ofFiniteSupport (fun j => if j = i then 1 else 0) (by
    apply (Set.finite_singleton i).subset
    intro j hj
    simpa [Function.mem_support] using hj)

/--
@isnad1 id=eq.0h4v.s7.717b2a02bd9a from=translated src=- shape=0bd308a5 vocab=435e9fb0
-/
@[simp] theorem coordinate_apply (i j : I) :
    coordinate (K := K) i j = if j = i then 1 else 0 := by
  classical
  rfl

omit [DiscreteTopology I] in
/-- Pointwise values are bounded by the sup norm.
@isnad1 id=le.0h4v.s7.c0891b4a9a43 from=translated src=- shape=dfbe9349 vocab=fc0bc1e1
-/
theorem norm_apply_le (x : C₀(I, K)) (i : I) : ‖x i‖ ≤ ‖x‖ :=
  BoundedContinuousFunction.norm_coe_le_norm x.toBCF i

omit [DiscreteTopology I] in
/-- The sup norm is at most `C` iff every value is.
@isnad1 id=iff.1h4v.s7.78bbf0cb0cae from=translated src=- shape=29be912a vocab=fc0bc1e1
-/
theorem norm_le {x : C₀(I, K)} {C : ℝ} (hC : 0 ≤ C) :
    ‖x‖ ≤ C ↔ ∀ i, ‖x i‖ ≤ C :=
  BoundedContinuousFunction.norm_le hC

/--
@isnad1 id=le.0h3v.s6.970bdb27f90e from=translated src=- shape=a716ec49 vocab=54971aa7
-/
theorem norm_coordinate_le (i : I) : ‖coordinate (K := K) i‖ ≤ 1 := by
  classical
  apply (norm_le zero_le_one).mpr
  intro j
  simp only [coordinate_apply]
  split_ifs <;> simp

/-- Continuous linear coordinate evaluation.-/
def evalCLM (i : I) : C₀(I, K) →L[K] K :=
  ({ toFun := fun x => x i
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : C₀(I, K) →ₗ[K] K).mkContinuous 1
       (fun x => by simpa using norm_apply_le x i)

omit [DiscreteTopology I] in
/--
@isnad1 id=eq.0h4v.s9.d6de81edcd46 from=translated src=- shape=2018df84 vocab=af506f4e
-/
@[simp] theorem evalCLM_apply (i : I) (x : C₀(I, K)) : evalCLM i x = x i := rfl

omit [DiscreteTopology I] in
/--
@isnad1 id=le.0h3v.s8.5860da2d97eb from=translated src=- shape=7456659a vocab=efa34bb5
-/
theorem norm_evalCLM_le (i : I) : ‖evalCLM (K := K) i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Keep the coordinates in the finite set `s` and set the others to zero.-/
def truncate (s : Finset I) (x : C₀(I, K)) : C₀(I, K) := by
  classical
  exact ofFiniteSupport (fun i => if i ∈ s then x i else 0) (by
    apply s.finite_toSet.subset
    intro i hi
    have h : i ∈ s ∧ x i ≠ 0 := by simpa [Function.mem_support] using hi
    exact h.1)

/--
@isnad1 id=eq.0h5v.s7.1372bfab8342 from=translated src=- shape=52c86036 vocab=b92a0a32
-/
@[simp] theorem truncate_apply (s : Finset I) (x : C₀(I, K)) (i : I) :
    truncate s x i = if i ∈ s then x i else 0 := by
  classical
  rfl

/--
@isnad1 id=hasfinit.0h4v.s7.90a1df62a2ac from=translated src=- shape=06e0e182 vocab=8d6deb70
-/
theorem truncate_hasFiniteSupport (s : Finset I) (x : C₀(I, K)) :
    (truncate s x : I → K).HasFiniteSupport := by
  classical
  apply s.finite_toSet.subset
  intro i hi
  by_contra his
  have his' : i ∉ s := his
  simp [Function.mem_support, his'] at hi

/--
@isnad1 id=le.0h4v.s7.35dcb13571ee from=translated src=- shape=7f60be96 vocab=58d4a38e
-/
theorem norm_truncate_le (s : Finset I) (x : C₀(I, K)) : ‖truncate s x‖ ≤ ‖x‖ := by
  classical
  apply (norm_le (norm_nonneg x)).mpr
  intro i
  by_cases hi : i ∈ s
  · simpa [hi] using norm_apply_le x i
  · simp [hi]

/-- Finite truncation as a continuous linear contraction.-/
def truncation (s : Finset I) : C₀(I, K) →L[K] C₀(I, K) :=
  ({ toFun := truncate s
     map_add' := by
       classical
       intro x y
       ext i
       by_cases hi : i ∈ s <;> simp [hi]
     map_smul' := by
       classical
       intro a x
       ext i
       by_cases hi : i ∈ s <;> simp [hi] } : C₀(I, K) →ₗ[K] C₀(I, K)).mkContinuous 1
         (fun x => by simpa using norm_truncate_le s x)

/--
@isnad1 id=eq.0h4v.s10.9cbff4c190e8 from=translated src=- shape=9dea1bc4 vocab=a12400fc
-/
@[simp] theorem truncation_apply (s : Finset I) (x : C₀(I, K)) :
    truncation s x = truncate s x := rfl

/--
@isnad1 id=le.0h3v.s9.92ac8f160c58 from=translated src=- shape=38642216 vocab=ad9daf79
-/
theorem norm_truncation_le (s : Finset I) : ‖truncation (K := K) s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- A truncation is the finite sum of its coordinates.
@isnad1 id=eq.0h4v.s10.c0f3a173c15b from=translated src=- shape=985a9185 vocab=6aadb01b
-/
theorem truncation_eq_sum (s : Finset I) (x : C₀(I, K)) :
    truncation s x = ∑ i ∈ s, x i • coordinate (K := K) i := by
  classical
  ext j
  change truncate s x j = evalCLM j (∑ i ∈ s, x i • coordinate (K := K) i)
  rw [map_sum]
  simp [map_smul, mul_ite]

/-- An element of `C₀(I, K)` tends to zero along the cofinite filter.
@isnad1 id=tendsto.0h3v.s7.dc4e67aca5c7 from=translated src=- shape=0cddc236 vocab=1d1f8a36
-/
theorem tendsto_cofinite (x : C₀(I, K)) : Tendsto x cofinite (𝓝 0) := by
  simpa only [Filter.cocompact_eq_cofinite] using zero_at_infty x

/-- Finite truncations converge in the supremum norm along all finite subsets.
@isnad1 id=tendsto.0h3v.s10.94e18bed2f45 from=translated src=- shape=f58521fe vocab=67e78e8b
-/
theorem tendsto_truncation (x : C₀(I, K)) :
    Tendsto (fun s : Finset I => truncation s x) atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ i in cofinite, ‖x i‖ < ε / 2 := by
    simpa only [dist_zero_right] using
      (Metric.tendsto_nhds.mp (tendsto_cofinite x) (ε / 2) (half_pos hε))
  have hfin : {i | ¬‖x i‖ < ε / 2}.Finite := eventually_cofinite.mp hsmall
  filter_upwards [eventually_ge_atTop hfin.toFinset] with s hs
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rw [dist_eq_norm]
  apply (norm_le (half_pos hε).le).mpr
  intro i
  by_cases hi : i ∈ s
  · simp [hi, (half_pos hε).le]
  · have hxi : ‖x i‖ < ε / 2 := by
      by_contra h
      exact hi (hs (hfin.mem_toFinset.mpr h))
    simpa [hi] using hxi.le

/-- Finitely supported vectors are dense.
@isnad1 id=dense.0h2v.s8.66fa6ced613d from=translated src=- shape=ce0196f7 vocab=1d959c52
-/
theorem dense_finiteSupport :
    Dense {x : C₀(I, K) | (x : I → K).HasFiniteSupport} := by
  intro x
  exact mem_closure_of_tendsto (tendsto_truncation x)
    (Eventually.of_forall fun s => truncate_hasFiniteSupport s x)

/-- Summary of this file: coordinates and truncations are contractions, truncations
converge, and finitely supported vectors are dense.
@isnad1 id=and.0h2v.s12.bd4c8f7d2953 from=translated src=- shape=8275a3b9 vocab=431fdaf3
-/
theorem coordinate_calculus :
    (∀ i j : I, coordinate (K := K) i j = if j = i then 1 else 0) ∧
    (∀ i : I, ‖coordinate (K := K) i‖ ≤ 1) ∧
    (∀ (i : I) (x : C₀(I, K)), evalCLM i x = x i) ∧
    (∀ i : I, ‖evalCLM (K := K) i‖ ≤ 1) ∧
    (∀ (s : Finset I) (x : C₀(I, K)) (i : I),
      truncation s x i = if i ∈ s then x i else 0) ∧
    (∀ s : Finset I, ‖truncation (K := K) s‖ ≤ 1) ∧
    (∀ (s : Finset I) (x : C₀(I, K)),
      truncation s x = ∑ i ∈ s, x i • coordinate (K := K) i) ∧
    (∀ (s : Finset I) (x : C₀(I, K)), (truncation s x : I → K).HasFiniteSupport) ∧
    (∀ x : C₀(I, K), Tendsto (fun s : Finset I => truncation s x) atTop (𝓝 x)) ∧
    Dense {x : C₀(I, K) | (x : I → K).HasFiniteSupport} := by
  exact ⟨coordinate_apply, norm_coordinate_le, evalCLM_apply, norm_evalCLM_le,
    fun s x i => truncate_apply s x i, norm_truncation_le, truncation_eq_sum,
    truncate_hasFiniteSupport, tendsto_truncation, dense_finiteSupport⟩

end CZero
