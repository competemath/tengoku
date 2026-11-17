import Tengoku.Seed.Analysis.Normed.Lp.lpSpace
import Tengoku.Seed.Analysis.Normed.Operator.LinearIsometry
import Tengoku.Seed.Analysis.Normed.Operator.Basic
import Tengoku.Seed.Topology.Algebra.Module.Basic
import Tengoku.Seed.Analysis.SpecificLimits.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dependent c₀ sums

The space `c₀({E i})` of families `x i ∈ E i` with `‖x i‖ → 0`, defined as the
closed span of coordinate vectors in `lp E ∞` with the supremum norm. It is used
in Appendix G with `E n = T_(n+1)(P)`, so the coordinates `n < N` hold tensor
degrees 1 through `N`.
-/

noncomputable section
namespace Tengoku.AlternatingAnalyticCharacteristicP end Tengoku.AlternatingAnalyticCharacteristicP open Tengoku.AlternatingAnalyticCharacteristicP 
open Filter
open scoped Topology BigOperators ENNReal NNReal

section Construction

variable (K : Type*) {I : Type*} (E : I → Type*)
  [NontriviallyNormedField K] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace K (E i)]

/-- The linear span of the dependent coordinate vectors in ℓ∞.-/
def _root_.Tengoku.AlternatingAnalyticCharacteristicP.dependentCZeroSpan : Submodule K (lp E ∞) := by
  classical
  exact Submodule.span K {x | ∃ i, ∃ v : E i, x = lp.single ∞ i v}

/-- The closed linear span of the dependent coordinate vectors in ℓ∞.-/
def _root_.Tengoku.AlternatingAnalyticCharacteristicP.dependentCZeroSubmodule : Submodule K (lp E ∞) :=
  (dependentCZeroSpan K E).topologicalClosure

/-- The dependent c₀ sum, with the norm inherited from dependent ℓ∞.-/
abbrev _root_.Tengoku.AlternatingAnalyticCharacteristicP.DependentCZero := ↥(dependentCZeroSubmodule K E)

namespace Tengoku.AlternatingAnalyticCharacteristicP.DependentCZero

variable {K E}

instance : CoeFun (DependentCZero K E) (fun _ => ∀ i, E i) :=
  ⟨fun x => (x.val : ∀ i, E i)⟩

@[ext]
theorem ext {x y : DependentCZero K E} (h : ∀ i, x i = y i) : x = y :=
  Subtype.ext (lp.ext (funext h))

@[simp] theorem zero_apply (i : I) : (0 : DependentCZero K E) i = 0 := rfl
@[simp] theorem add_apply (x y : DependentCZero K E) (i : I) :
    (x + y) i = x i + y i := rfl
@[simp] theorem sub_apply (x y : DependentCZero K E) (i : I) :
    (x - y) i = x i - y i := rfl
@[simp] theorem smul_apply (a : K) (x : DependentCZero K E) (i : I) :
    (a • x) i = a • x i := rfl

/-- The ambient inclusion is a linear isometry.-/
def toLp : DependentCZero K E →ₗᵢ[K] lp E ∞ :=
  (dependentCZeroSubmodule K E).subtypeₗᵢ

@[simp] theorem toLp_apply (x : DependentCZero K E) : toLp x = x.val := rfl

/-- The norm is the supremum of the coordinate norms (zero for an empty index type).-/
theorem norm_eq (x : DependentCZero K E) : ‖x‖ = ⨆ i, ‖x i‖ :=
  lp.norm_eq_ciSup x.val

theorem norm_apply_le_norm (x : DependentCZero K E) (i : I) : ‖x i‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x.val i

theorem single_mem (i : I) (v : E i) :
    letI := Classical.decEq I
    lp.single ∞ i v ∈ dependentCZeroSubmodule K E := by
  classical
  exact (dependentCZeroSpan K E).le_topologicalClosure
    (Submodule.subset_span ⟨i, v, rfl⟩)

/-- The coordinate injection, obtained by restricting the codomain of Mathlib's map.-/
def single (i : I) : E i →L[K] DependentCZero K E := by
  classical
  exact (lp.singleContinuousLinearMap K E ∞ i).codRestrict
    (dependentCZeroSubmodule K E) (single_mem i)

@[simp] theorem single_apply (i : I) (v : E i) (j : I) :
    letI := Classical.decEq I
    single (K := K) (E := E) i v j = Pi.single i v j := rfl

@[simp] theorem single_apply_self (i : I) (v : E i) :
    single (K := K) (E := E) i v i = v := by
  classical
  exact lp.single_apply_self ∞ i v

theorem single_apply_ne (i : I) (v : E i) {j : I} (h : j ≠ i) :
    single (K := K) (E := E) i v j = 0 := by
  classical
  exact lp.single_apply_ne ∞ i v h

@[simp] theorem norm_single (i : I) (v : E i) :
    ‖single (K := K) (E := E) i v‖ = ‖v‖ := by
  classical
  exact lp.norm_single (by simp) i v

/-- Coordinate projection, the restriction of Mathlib's evaluation map.-/
def eval (i : I) : DependentCZero K E →L[K] E i :=
  (lp.evalCLM K E ∞ i).comp (dependentCZeroSubmodule K E).subtypeL

@[simp] theorem eval_apply (i : I) (x : DependentCZero K E) : eval i x = x i := rfl

@[simp] theorem eval_comp_single (i : I) :
    (eval (K := K) (E := E) i).comp (single i) = ContinuousLinearMap.id K (E i) := by
  ext v
  exact single_apply_self (K := K) i v

/-- A finite vector with the prescribed dependent coordinates.-/
def finiteVector (s : Finset I) (v : ∀ i, E i) : DependentCZero K E :=
  ∑ i ∈ s, single i (v i)

@[simp] theorem finiteVector_apply (s : Finset I) (v : ∀ i, E i) (i : I) :
    letI := Classical.decEq I
    finiteVector (K := K) s v i = if i ∈ s then v i else 0 := by
  classical
  change eval i (∑ j ∈ s, single j (v j)) = _
  simp only [map_sum, eval_apply, single_apply, Finset.sum_pi_single]

/-- Finite-subset truncation as a continuous linear endomorphism.-/
def truncate (s : Finset I) : DependentCZero K E →L[K] DependentCZero K E :=
  ∑ i ∈ s, (single i).comp (eval i)

theorem truncate_eq_finiteVector (s : Finset I) (x : DependentCZero K E) :
    truncate s x = finiteVector s x := by
  simp [truncate, finiteVector]

@[simp] theorem truncate_apply (s : Finset I) (x : DependentCZero K E) (i : I) :
    letI := Classical.decEq I
    truncate s x i = if i ∈ s then x i else 0 := by
  classical
  rw [truncate_eq_finiteVector, finiteVector_apply]

/-- Every vector in the algebraic coordinate span has finite support.-/
theorem finite_support_of_mem_span (x : lp E ∞) (hx : x ∈ dependentCZeroSpan K E) :
    ∃ s : Finset I, ∀ i ∉ s, x i = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, v, rfl⟩ := hx
    refine ⟨{i}, fun j hj => ?_⟩
    exact lp.single_apply_ne _ _ _ (by simpa using hj)
  | zero => exact ⟨∅, by simp⟩
  | add x y hx hy hx' hy' =>
    obtain ⟨s, hs⟩ := hx'
    obtain ⟨t, ht⟩ := hy'
    refine ⟨s ∪ t, fun i hi => ?_⟩
    have his : i ∉ s := fun h => hi (Finset.mem_union_left _ h)
    have hit : i ∉ t := fun h => hi (Finset.mem_union_right _ h)
    simp [hs i his, ht i hit]
  | smul a x hx hx' =>
    obtain ⟨s, hs⟩ := hx'
    exact ⟨s, fun i hi => by simp [lp.coeFn_smul, hs i hi]⟩

/-- Coordinate formula for ambient finite truncations.-/
theorem ambient_sum_single_apply [DecidableEq I] (s : Finset I) (v : ∀ i, E i) (i : I) :
    (∑ j ∈ s, lp.single ∞ j (v j)) i = if i ∈ s then v i else 0 := by
  classical
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]

/-- The closed coordinate span consists of the families with `‖x i‖ → 0` along `cofinite`.-/
theorem mem_iff (x : lp E ∞) :
    x ∈ dependentCZeroSubmodule K E ↔
      Tendsto (fun i => ‖x i‖) cofinite (𝓝 0) := by
  classical
  constructor
  · intro hx
    change x ∈ closure (dependentCZeroSpan K E : Set (lp E ∞)) at hx
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
    obtain ⟨s, hs⟩ := finite_support_of_mem_span y hy
    filter_upwards [s.eventually_cofinite_notMem] with i hi
    have hbound := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (x - y) i
    have hn : ‖x i‖ < ε := by
      have heq : (x - y) i = x i := by simp [hs i hi]
      rw [heq] at hbound
      exact lt_of_le_of_lt hbound (by simpa [dist_eq_norm] using hxy)
    simpa using hn
  · intro hx
    change x ∈ closure (dependentCZeroSpan K E : Set (lp E ∞))
    rw [Metric.mem_closure_iff]
    intro ε hε
    have he : ∀ᶠ i in cofinite, ‖x i‖ < ε / 2 :=
      hx.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
    let s : Finset I := (eventually_cofinite.mp he).toFinset
    have hs : ∀ i ∉ s, ‖x i‖ < ε / 2 := by
      intro i hi
      simpa [s] using hi
    refine ⟨∑ i ∈ s, lp.single ∞ i (x i), ?_, ?_⟩
    · apply Submodule.sum_mem
      intro i hi
      exact Submodule.subset_span ⟨i, x i, rfl⟩
    · rw [dist_eq_norm]
      refine lt_of_le_of_lt (lp.norm_le_of_forall_le (by positivity) ?_) (half_lt_self hε)
      intro i
      rw [lp.coeFn_sub, Pi.sub_apply, ambient_sum_single_apply]
      split_ifs with hi
      · simpa using (le_of_lt (half_pos hε))
      · simpa using le_of_lt (hs i hi)

/-- Every c₀ vector has coordinate norms tending to zero along `cofinite`.-/
theorem tendsto_norm (x : DependentCZero K E) :
    Tendsto (fun i => ‖x i‖) cofinite (𝓝 0) :=
  (mem_iff x.val).mp x.property

end Tengoku.AlternatingAnalyticCharacteristicP.DependentCZero

end Construction

namespace Tengoku.AlternatingAnalyticCharacteristicP.DependentCZero

section CoordinateSubspaces

variable {K : Type*} {I : Type*} {E : I → Type*}
  [NontriviallyNormedField K] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace K (E i)]
variable (D : ∀ i, Submodule K (E i))

/-- The coordinatewise submodule of dependent `c₀` associated with `D`.-/
def coordinateSubmodule : Submodule K (DependentCZero K E) :=
  ⨅ i, (D i).comap (eval (K := K) (E := E) i).toLinearMap

@[simp]
theorem mem_coordinateSubmodule (x : DependentCZero K E) :
    x ∈ coordinateSubmodule D ↔ ∀ i, x i ∈ D i := by
  simp [coordinateSubmodule]

/-- Coordinatewise inclusion of dependent `c₀` sums is isometric.-/
def coordinateInclusion : DependentCZero K (fun i ↦ D i) →ₗᵢ[K] DependentCZero K E where
  toFun x :=
    ⟨⟨fun i ↦ (x i : E i), memℓp_infty ⟨‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact norm_apply_le_norm x i⟩⟩,
      (mem_iff _).2 (by simpa using tendsto_norm x)⟩
  map_add' x y := by
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl
  map_smul' a x := by
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl
  norm_map' x := by
    rw [norm_eq, norm_eq]
    rfl

@[simp]
theorem coordinateInclusion_apply (x : DependentCZero K (fun i ↦ D i)) (i : I) :
    coordinateInclusion D x i = (x i : E i) := rfl

/-- Regard a vector whose coordinates lie in `D` as a vector in the dependent sum of `D`.-/
def coordinateRestriction (x : coordinateSubmodule D) : DependentCZero K (fun i ↦ D i) :=
  ⟨⟨fun i ↦ ⟨(x : DependentCZero K E) i, (mem_coordinateSubmodule D _).1 x.property i⟩,
      memℓp_infty ⟨‖(x : DependentCZero K E)‖, by
        rintro _ ⟨i, rfl⟩
        exact norm_apply_le_norm (x : DependentCZero K E) i⟩⟩,
    (mem_iff _).2 (by simpa using tendsto_norm (x : DependentCZero K E))⟩

@[simp]
theorem coordinateRestriction_apply (x : coordinateSubmodule D) (i : I) :
    (coordinateRestriction D x i : E i) = (x : DependentCZero K E) i := rfl

/-- The `c₀` sum of the subspaces `D i` is isometric to the coordinatewise submodule.-/
def coordinateEquiv :
    DependentCZero K (fun i ↦ D i) ≃ₗᵢ[K] coordinateSubmodule D where
  toFun x := ⟨coordinateInclusion D x,
    (mem_coordinateSubmodule D _).2 fun i ↦ (x i).property⟩
  invFun := coordinateRestriction D
  map_add' x y := by
    apply Subtype.ext
    exact map_add (coordinateInclusion D) x y
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul (coordinateInclusion D) a x
  left_inv x := by
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl
  norm_map' x := (coordinateInclusion D).norm_map x

@[simp]
theorem coordinateEquiv_apply (x : DependentCZero K (fun i ↦ D i)) :
    (coordinateEquiv D x : DependentCZero K E) = coordinateInclusion D x := rfl

@[simp]
theorem coordinateEquiv_symm_apply (x : coordinateSubmodule D) :
    (coordinateEquiv D).symm x = coordinateRestriction D x := rfl

instance coordinateSubmoduleNormedAddCommGroup : NormedAddCommGroup (coordinateSubmodule D) :=
  inferInstance

instance coordinateSubmoduleNormedSpace : NormedSpace K (coordinateSubmodule D) :=
  inferInstance

/-- Projection from the concrete coordinate subspace onto one of its fibers.-/
def coordinateEval (i : I) : coordinateSubmodule D →L[K] D i :=
  ((eval (K := K) (E := E) i).comp (coordinateSubmodule D).subtypeL).codRestrict
    (D i) (fun x ↦ (mem_coordinateSubmodule D _).1 x.property i)

@[simp]
theorem coordinateEval_apply (i : I) (x : coordinateSubmodule D) :
    (coordinateEval D i x : E i) = (x : DependentCZero K E) i := rfl

end CoordinateSubspaces

end Tengoku.AlternatingAnalyticCharacteristicP.DependentCZero

/- Geometric bounds for `ℕ`-indexed families. The convention starts in degree one:
the `n`-th coordinate is bounded by `C * r^(n+1)`. -/

namespace Tengoku.AlternatingAnalyticCharacteristicP.DependentCZero

section Geometric

variable {K : Type*} [NontriviallyNormedField K]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
variable [∀ n, NormedSpace K (E n)]

private lemma geometric_bound_le {C r : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r)
    (hr₁ : r < 1) (n : ℕ) : C * r ^ (n + 1) ≤ C := by
  have hp : r ^ (n + 1) ≤ 1 := pow_le_one₀ hr₀ hr₁.le
  simpa using mul_le_mul_of_nonneg_left hp hC

private lemma geometric_memℓp (v : ∀ n, E n) {C r : ℝ} (hC : 0 ≤ C)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1)) :
    Memℓp v ∞ := by
  apply memℓp_infty
  refine ⟨C, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (hv n).trans (geometric_bound_le hC hr₀ hr₁ n)

/-- The bound for the coordinate convention starting in degree one tends to zero.-/
theorem tendsto_geometric_bound {C r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Tendsto (fun n : ℕ => C * r ^ (n + 1)) atTop (𝓝 0) := by
  simpa only [mul_zero, Function.comp_def] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).comp
      (tendsto_add_atTop_nat 1)).const_mul C

private lemma geometric_tendsto (v : ∀ n, E n) {C r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1)) :
    Tendsto (fun n => ‖v n‖) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  exact squeeze_zero (fun n => norm_nonneg _) hv (tendsto_geometric_bound hr₀ hr₁)

/-- A family with geometric coordinate bounds, as an element of c₀.-/
def ofGeometric (v : ∀ n, E n) {C r : ℝ} (hC : 0 ≤ C)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1)) :
    DependentCZero K E :=
  ⟨⟨v, geometric_memℓp v hC hr₀ hr₁ hv⟩,
    (mem_iff _).2 (geometric_tendsto v hr₀ hr₁ hv)⟩

@[simp] theorem ofGeometric_apply (v : ∀ n, E n) {C r : ℝ} (hC : 0 ≤ C)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1))
    (n : ℕ) : ofGeometric (K := K) v hC hr₀ hr₁ hv n = v n := rfl

/-- Reconstruct a family from coordinate values on a set, extending by zero outside it.-/
noncomputable def ofGeometricOn {X : Type*} (v : X → ∀ n, E n) (A : Set X)
    {C r : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hv : ∀ x ∈ A, ∀ n, ‖v x n‖ ≤ C * r ^ (n + 1)) :
    X → DependentCZero K E := by
  classical
  exact fun x => if hx : x ∈ A then ofGeometric (v x) hC hr₀ hr₁ (hv x hx) else 0

@[simp] theorem ofGeometricOn_apply {X : Type*} (v : X → ∀ n, E n) (A : Set X)
    {C r : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hv : ∀ x ∈ A, ∀ n, ‖v x n‖ ≤ C * r ^ (n + 1)) (x : X) (hx : x ∈ A)
    (n : ℕ) : ofGeometricOn (K := K) v A hC hr₀ hr₁ hv x n = v x n := by
  classical
  simp [ofGeometricOn, hx]

end Geometric

end Tengoku.AlternatingAnalyticCharacteristicP.DependentCZero
-- Tengoku: root names of this library moved to Tengoku.AlternatingAnalyticCharacteristicP so they do not collide with other libraries (generated)
