import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.DetectingSequence

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def halfWeight (j : ℕ) : ℝ := (1/2:ℝ)^(j+1)

theorem halfWeight_pos (j : ℕ) : 0 < halfWeight j := by unfold halfWeight; positivity

theorem sum_halfWeight (n : ℕ) : ∑ j ∈ Finset.range n, halfWeight j = 1-(1/2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [halfWeight,pow_succ]; ring

theorem sum_halfWeight_le (n : ℕ) : (∑ j ∈ Finset.range n, halfWeight j) ≤ 1 := by
  rw [sum_halfWeight]
  linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

theorem halfWeight_le_one (j : ℕ) : halfWeight j ≤ 1 := by
  unfold halfWeight
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem damping_telescope (z : ℕ → Smooth H) (n : ℕ) (x : H) :
    (∑ j ∈ Finset.range n, damping (Finset.range j) z x * ‖Smooth.grad x (z j)‖) =
      1-damping (Finset.range n) z x := by
  induction n with
  | zero => simp [damping]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    have hd : damping (Finset.range (n+1)) z x = damping (Finset.range n) z x *
        (1-‖Smooth.grad x (z n)‖) := Finset.prod_range_succ _ n
    rw [hd]
    ring

theorem sum_grad_norm_le {Q : Set H} (z w : ℕ → Smooth H) (ε : ℕ → ℝ)
    (hz : ∀ i, LipschitzWith 1 (z i).val)
    (hεsum : ∀ n, (∑ i ∈ Finset.range n, ε i) ≤ 1)
    (herr : ∀ i x, x ∈ Q →
      ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ ≤ ε i)
    (n : ℕ) {x : H} (hx : x ∈ Q) : (∑ i ∈ Finset.range n, ‖Smooth.grad x (w i)‖) ≤ 2 := by
  have h (i : ℕ) : ‖Smooth.grad x (w i)‖ ≤
      damping (Finset.range i) z x * ‖Smooth.grad x (z i)‖+ε i := by
    have hd := damping_nonneg (Finset.range i) z (fun j _ => hz j) x
    calc
      _ ≤ ‖damping (Finset.range i) z x • Smooth.grad x (z i)‖+
          ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ := norm_le_insert' _ _
      _ ≤ _ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]; exact add_le_add le_rfl (herr i x hx)
  calc
    _ ≤ ∑ i ∈ Finset.range n, (damping (Finset.range i) z x * ‖Smooth.grad x (z i)‖+ε i) :=
      Finset.sum_le_sum (fun i _ => h i)
    _ = 1-damping (Finset.range n) z x+∑ i ∈ Finset.range n, ε i := by
      rw [Finset.sum_add_distrib,damping_telescope]
    _ ≤ 2 := by linarith [damping_nonneg (Finset.range n) z (fun j _ => hz j) x,hεsum n]

theorem signed_sum_lipschitz {Q : Set H} (hQ : Convex ℝ Q) (w : ℕ → Smooth H)
    (hgrad : ∀ n x, x ∈ Q → (∑ i ∈ Finset.range n, ‖Smooth.grad x (w i)‖) ≤ 2)
    (n : ℕ) (c : ℕ → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    LipschitzOnWith 2 (fun x => ∑ i ∈ Finset.range n, c i*(w i).val x) Q := by
  let f : Smooth H := ∑ i ∈ Finset.range n, c i • w i
  have hef (x : H) : f.val x = ∑ i ∈ Finset.range n, c i*(w i).val x := by
    change Smooth.eval x f = _
    simp only [f,map_sum,map_smul,smul_eq_mul,Smooth.eval,LinearMap.coe_mk,AddHom.coe_mk]
  have hfn : LipschitzOnWith 2 f.val Q := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => f.differentiable x) _ hQ
    intro x hx
    rw [← NNReal.coe_le_coe]
    change ‖fderiv ℝ f.val x‖ ≤ (2:ℝ)
    rw [← Smooth.norm_grad]
    calc
      _ = ‖∑ i ∈ Finset.range n, c i • Smooth.grad x (w i)‖ := by simp only [f,map_sum,map_smul]
      _ ≤ ∑ i ∈ Finset.range n, ‖c i • Smooth.grad x (w i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, ‖Smooth.grad x (w i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hc i)
      _ ≤ 2 := hgrad n x hx
  have he : f.val = (fun x => ∑ i ∈ Finset.range n, c i*(w i).val x) := funext hef
  rw [he] at hfn
  exact hfn

end LipschitzCounterexample.CompactWSC
end

end OAI
