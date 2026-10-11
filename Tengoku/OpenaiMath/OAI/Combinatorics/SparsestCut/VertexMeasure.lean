import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.ContractionAverage

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.VertexMeasure
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => (CubePoincare.cube (m:=m))
local instance {u : Fin S → Fin N → E} {τ : ℝ} : MeasurableSpace (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
local instance {u : Fin S → Fin N → E} {τ : ℝ} : MeasurableSingletonClass (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
lemma cube_measurable (R : ℝ) : MeasurableSet (RoundedCharts.cube (m:=m) R) := by
  rw [show RoundedCharts.cube (m:=m) R=(⋂ j : Fin m, {x : E | |x j|<R}) by ext x; simp [RoundedCharts.cube]]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_lt (by fun_prop) measurable_const
lemma regular_measurable (u : Fin N → E) (τ : ℝ) : MeasurableSet {x | RoundedCharts.regular u τ x} := by
  rw [show {x | RoundedCharts.regular u τ x}=(⋂ i : Fin N, ⋂ k : ℤ, {x : E | inner ℝ (u i) x ≠ (k:ℝ)*τ}) by ext x; simp [RoundedCharts.regular]]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro k
  exact (isClosed_eq (by fun_prop : Continuous (fun x : E => inner ℝ (u i) x)) continuous_const).measurableSet.compl
open Classical in
def label (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) (x : E) : RoundedCharts.Vertex u τ :=
  if h : x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u s) τ x then
    ⟨(s,RoundedCharts.integerLabel (u s) τ x),x,h.1,h.2,rfl⟩ else v₀
def measure (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) : Measure (RoundedCharts.Vertex u τ) :=
  (μ).map (label u τ s v₀)
lemma finite_weights {V : Type u1} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : Measure V) [IsProbabilityMeasure ν] : (∑ v, ν.real {v})=1 := by
  have h : (∫ _ : V, (1:ℝ) ∂ν)=∑ v, ν.real {v} • (1:ℝ) := integral_fintype (integrable_const _)
  simp
end
end UniformSparsestCut.VertexMeasure

end

end OAI
