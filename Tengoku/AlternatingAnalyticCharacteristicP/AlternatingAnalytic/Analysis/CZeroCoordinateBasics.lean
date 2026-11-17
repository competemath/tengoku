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

@[simp] theorem ofFiniteSupport_apply (f : I → K) (hf : f.HasFiniteSupport) (i : I) :
    ofFiniteSupport f hf i = f i := rfl

/-- The coordinate vector supported at `i`, with value one there.-/
def coordinate (i : I) : C₀(I, K) := by
  classical
  exact ofFiniteSupport (fun j => if j = i then 1 else 0) (by
    apply (Set.finite_singleton i).subset
    intro j hj
    simpa [Function.mem_support] using hj)

@[simp] theorem coordinate_apply (i j : I) :
    coordinate (K := K) i j = if j = i then 1 else 0 := by
  classical
  rfl

omit [DiscreteTopology I] in
/-- Pointwise values are bounded by the sup norm.-/
theorem norm_apply_le (x : C₀(I, K)) (i : I) : ‖x i‖ ≤ ‖x‖ :=
  BoundedContinuousFunction.norm_coe_le_norm x.toBCF i

omit [DiscreteTopology I] in
/-- The sup norm is at most `C` iff every value is.-/
theorem norm_le {x : C₀(I, K)} {C : ℝ} (hC : 0 ≤ C) :
    ‖x‖ ≤ C ↔ ∀ i, ‖x i‖ ≤ C :=
  BoundedContinuousFunction.norm_le hC

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
@[simp] theorem evalCLM_apply (i : I) (x : C₀(I, K)) : evalCLM i x = x i := rfl

omit [DiscreteTopology I] in
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

@[simp] theorem truncate_apply (s : Finset I) (x : C₀(I, K)) (i : I) :
    truncate s x i = if i ∈ s then x i else 0 := by
  classical
  rfl

theorem truncate_hasFiniteSupport (s : Finset I) (x : C₀(I, K)) :
    (truncate s x : I → K).HasFiniteSupport := by
  classical
  apply s.finite_toSet.subset
  intro i hi
  by_contra his
  have his' : i ∉ s := his
  simp [Function.mem_support, his'] at hi

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

@[simp] theorem truncation_apply (s : Finset I) (x : C₀(I, K)) :
    truncation s x = truncate s x := rfl

theorem norm_truncation_le (s : Finset I) : ‖truncation (K := K) s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- A truncation is the finite sum of its coordinates.-/
theorem truncation_eq_sum (s : Finset I) (x : C₀(I, K)) :
    truncation s x = ∑ i ∈ s, x i • coordinate (K := K) i := by
  classical
  ext j
  change truncate s x j = evalCLM j (∑ i ∈ s, x i • coordinate (K := K) i)
  rw [map_sum]
  simp [map_smul, mul_ite]

/-- An element of `C₀(I, K)` tends to zero along the cofinite filter.-/
theorem tendsto_cofinite (x : C₀(I, K)) : Tendsto x cofinite (𝓝 0) := by
  simpa only [Filter.cocompact_eq_cofinite] using zero_at_infty x

/-- Finite truncations converge in the supremum norm along all finite subsets.-/
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

/-- Finitely supported vectors are dense.-/
theorem dense_finiteSupport :
    Dense {x : C₀(I, K) | (x : I → K).HasFiniteSupport} := by
  intro x
  exact mem_closure_of_tendsto (tendsto_truncation x)
    (Eventually.of_forall fun s => truncate_hasFiniteSupport s x)

/-- Summary of this file: coordinates and truncations are contractions, truncations
converge, and finitely supported vectors are dense.-/
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
