import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.Parameters

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceMetric
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m)
local notation "E" => EuclideanSpace ℝ (Fin m)
abbrev V := RoundedCharts.Vertex (u f) (p m 2000)
noncomputable instance vertexFintype [NeZero m] : Fintype (V f) := by
  letI := RoundedCharts.vertex_finite (u f) (τ := p m 2000) (p_pos (by exact_mod_cast NeZero.pos m) _) (fun s i => (u_norm f (NeZero.pos m) s i).2)
  exact Fintype.ofFinite _
def L : ℝ := GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
  (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)
def err : ℝ := GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
  (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0
end
end UniformSparsestCut.SourceMetric

namespace UniformSparsestCut.SourceMetric
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) [NeZero m]
local notation "E" => EuclideanSpace ℝ (Fin m)
def C₀ : ℝ := 9+2*KernelApprox.cstar
lemma C₀_pos : 0<C₀ := by unfold C₀; linarith [KernelApprox.cstar_pos]
def vertex (s : Fin (m^3)) (θ : E) (hθ : θ∈RoundedCharts.cube 2)
    (hs : RoundedCharts.regular (u f s) (p m 2000) θ) : V f :=
  ⟨(s,RoundedCharts.integerLabel (u f s) (p m 2000) θ),θ,hθ,hs,rfl⟩
omit [NeZero m] in
lemma near_norm (hm : 3000 ≤ m) : Real.sqrt m*p m 1997≤p m 8 := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  calc
    _ ≤ (m:ℝ)*p m 1997 := mul_le_mul_of_nonneg_right (sqrt_le hx) (p_nonneg (by positivity) _)
    _ = p m 1996 := p_succ (by positivity : (m:ℝ)≠0) 1996
    _ ≤ _ := p_le hx (by norm_num)
lemma macro_bound (hm : 3000 ≤ m) (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*
         ‖B f (NeZero.pos m) v.val.1 (RoundedCharts.coordinate (u f) (p m 2000) v)-
           B f (NeZero.pos m) w.val.1 (RoundedCharts.coordinate (u f) (p m 2000) w)‖|≤err (m:=m)+8*p m 8)
    (s t : Fin (m^3)) (θ η : E) (hθ : θ∈RoundedCharts.cube 2) (hη : η∈RoundedCharts.cube 2)
    (hs : RoundedCharts.regular (u f s) (p m 2000) θ)
    (ht : RoundedCharts.regular (u f t) (p m 2000) η) :
    |‖Z (vertex f s θ hθ hs)-Z (vertex f t η hη ht)‖^2-KernelApprox.cstar*Real.sqrt m*‖θ-η‖|≤C₀*p m 8 := by
  let v := vertex f s θ hθ hs
  let w := vertex f t η hη ht
  let X := B f (NeZero.pos m) s (RoundedCharts.rounded (u f s) (p m 2000) θ)
  let Y := B f (NeZero.pos m) t (RoundedCharts.rounded (u f t) (p m 2000) η)
  have hτ : 0<p m 2000 := p_pos (by exact_mod_cast NeZero.pos m) _
  have hx : ‖X-θ‖≤p m 1997 := by
    simpa only [rounded_radius (NeZero.pos m)] using rounded_B_error f (NeZero.pos m) (show 2 ≤ m by omega) hτ s θ
  have hy : ‖Y-η‖≤p m 1997 := by
    simpa only [rounded_radius (NeZero.pos m)] using rounded_B_error f (NeZero.pos m) (show 2 ≤ m by omega) hτ t η
  have hnorm : |‖X-Y‖-‖θ-η‖|≤2*p m 1997 := by
    calc
      _ ≤ ‖(X-Y)-(θ-η)‖ := abs_norm_sub_norm_le _ _
      _ = ‖(X-θ)-(Y-η)‖ := by congr 1; abel
      _ ≤ ‖X-θ‖+‖Y-η‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hM := hmac v w
  change |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*‖X-Y‖|≤err (m:=m)+8*p m 8 at hM
  have hq : 0≤KernelApprox.cstar*Real.sqrt m := mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (near_norm (m:=m) hm) (mul_nonneg (by norm_num : (0:ℝ)≤2) KernelApprox.cstar_pos.le)
  have he := macro_small hm
  change err (m:=m)≤p m 8/2 at he
  have hM' := abs_le.mp hM
  have hn' := abs_le.mp hnorm
  have hn1 := mul_le_mul_of_nonneg_left hn'.1 hq
  have hn2 := mul_le_mul_of_nonneg_left hn'.2 hq
  change |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*‖θ-η‖|≤_
  rw [abs_le]; unfold C₀
  constructor <;> nlinarith [p_nonneg (by positivity : (0:ℝ) ≤ m) 8]
lemma one_step (vp vm : V f) (i : Fin (m^6))
    (hi : vp.val.2 i=vm.val.2 i+1) (hj : ∀ j, j≠i → vp.val.2 j=vm.val.2 j) :
    (∑ j, |RoundedCharts.coordinate (u f) (p m 2000) vp j-
        RoundedCharts.coordinate (u f) (p m 2000) vm j|)=p m 2000 := by
  classical
  rw [Finset.sum_eq_single i]
  · change |p m 2000*(vp.val.2 i:ℝ)-p m 2000*(vm.val.2 i:ℝ)|=_
    rw [hi,Int.cast_add,Int.cast_one]
    have h : p m 2000*((vm.val.2 i:ℝ)+1)-p m 2000*(vm.val.2 i:ℝ)=p m 2000 := by ring
    rw [h,abs_of_pos (p_pos (by exact_mod_cast NeZero.pos m) _)]
  · intro j hmem hji
    change |p m 2000*(vp.val.2 j:ℝ)-p m 2000*(vm.val.2 j:ℝ)|=0
    rw [hj j hji,sub_self,abs_zero]
  · simp
end
end UniformSparsestCut.SourceMetric

end

end OAI
