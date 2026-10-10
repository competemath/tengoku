import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.BlockSelection

namespace OAI

universe uH uIndex

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def damping {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H) (x : H) : ℝ :=
  ∏ i ∈ s, (1-‖Smooth.grad x (z i)‖)

theorem damping_nonneg {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (x : H) : 0 ≤ damping s z x := by
  apply Finset.prod_nonneg
  intro i hi
  have h := (z i).grad_norm_le (hz i hi) x
  norm_num only [NNReal.coe_one] at h
  linarith

theorem product_gradient_error {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (φ f : Smooth H) {x : H} {D ε : ℝ}
    (hf : ‖Smooth.grad x f‖ ≤ 1) (hφ : ‖Smooth.grad x φ‖ ≤ D)
    (happrox : |φ.val x-damping s z x| ≤ ε/2)
    (hsmall : |f.val x| * D ≤ ε/2) :
    ‖Smooth.grad x (φ.mul f)-damping s z x • Smooth.grad x f‖ ≤ ε := by
  rw [Smooth.grad_mul]
  have he : φ.val x • Smooth.grad x f+f.val x • Smooth.grad x φ-
      damping s z x • Smooth.grad x f =
      (φ.val x-damping s z x) • Smooth.grad x f+f.val x • Smooth.grad x φ := by module
  rw [he]
  calc
    _ ≤ ‖(φ.val x-damping s z x) • Smooth.grad x f‖+‖f.val x • Smooth.grad x φ‖ := norm_add_le _ _
    _ = |φ.val x-damping s z x| * ‖Smooth.grad x f‖+|f.val x| * ‖Smooth.grad x φ‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ |φ.val x-damping s z x|+|f.val x| * D := by
      apply add_le_add
      · simpa using mul_le_mul_of_nonneg_left hf (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left hφ (abs_nonneg _)
    _ ≤ ε := by linarith

end LipschitzCounterexample.CompactWSC
end

end OAI
