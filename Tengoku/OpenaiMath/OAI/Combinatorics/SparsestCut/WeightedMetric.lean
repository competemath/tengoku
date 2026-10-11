import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.VertexMeasure

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceWeighted
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
open SourceCharts SourceParameters SourceMetric
noncomputable section
local instance {m N S : ℕ} {u : Fin S → Fin N → EuclideanSpace ℝ (Fin m)} {τ : ℝ} :
    MeasurableSpace (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
local instance {m N S : ℕ} {u : Fin S → Fin N → EuclideanSpace ℝ (Fin m)} {τ : ℝ} :
    MeasurableSingletonClass (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance

def D : ℝ := 4*KernelApprox.cstar+C₀
lemma D_pos : 0<D := by
  have hc := KernelApprox.cstar_pos
  have hr := C₀_pos
  unfold D
  positivity
lemma diameter {m : ℕ} [NeZero m] (f : PivotFamily.PFamily m) (hm : 3000 ≤ m)
    (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*
         ‖B f (NeZero.pos m) v.val.1 (RoundedCharts.coordinate (u f) (p m 2000) v)-
           B f (NeZero.pos m) w.val.1 (RoundedCharts.coordinate (u f) (p m 2000) w)‖|≤err (m:=m)+8*p m 8)
    (v w : V f) : ‖Z v-Z w‖^2≤D*m := by
  obtain ⟨θ,hθ,hr,he⟩ := v.property
  obtain ⟨η,hη,hs,hf⟩ := w.property
  have hv : vertex f v.val.1 θ hθ hr=v := by apply Subtype.ext; change (v.val.1,_)=(v.val.1,_); rw [he]
  have hw : vertex f w.val.1 η hη hs=w := by apply Subtype.ext; change (w.val.1,_)=(w.val.1,_); rw [hf]
  have hh := (abs_le.mp (macro_bound f hm Z hmac v.val.1 w.val.1 θ η hθ hη hr hs)).2
  rw [hv,hw] at hh
  have hn : ‖θ-η‖≤4*Real.sqrt m := by
    have h1 := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hθ
    have h2 := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hη
    have h3 := norm_sub_le θ η
    linarith
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : p m 8 ≤ (m:ℝ) := (p_one_le hx _).trans hx
  have hq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) m)
  have h1 := mul_le_mul_of_nonneg_left hn (mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg m))
  have h2 := mul_le_mul_of_nonneg_left hp C₀_pos.le
  have he : KernelApprox.cstar*Real.sqrt m*(4*Real.sqrt m)=4*KernelApprox.cstar*(m:ℝ) := by
    calc
      _ = 4*KernelApprox.cstar*(Real.sqrt m)^2 := by ring
      _ = _ := by rw [hq]
  rw [he] at h1
  unfold D
  linarith only [hh,h1,h2]

end
end UniformSparsestCut.SourceWeighted

end

end OAI
